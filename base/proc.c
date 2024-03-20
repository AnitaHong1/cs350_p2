#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include <stddef.h>

int child_bit;
int sched_policy;
int total_tickets = 100;

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

static struct proc *initproc;

int nextpid = 1;
int sched_trace_enabled = 0; // ZYF: for OS CPU/process project
int sched_trace_counter = 0; // ZYF: counter for print formatting
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Must be called with interrupts disabled
int
cpuid() {
  return mycpu()-cpus;
}

// Must be called with interrupts disabled to avoid the caller being
// rescheduled between reading lapicid and running through the loop.
struct cpu*
mycpu(void)
{
  int apicid, i;
  
  if(readeflags()&FL_IF)
    panic("mycpu called with interrupts enabled\n");
  
  apicid = lapicid();
  // APIC IDs are not guaranteed to be contiguous. Maybe we should have
  // a reverse map, or reserve a register to store &cpus[i].
  for (i = 0; i < ncpu; ++i) {
    if (cpus[i].apicid == apicid)
      return &cpus[i];
  }
  panic("unknown apicid\n");
}

// Disable interrupts so that we are not rescheduled
// while reading proc from the cpu structure
struct proc*
myproc(void) {
  struct cpu *c;
  struct proc *p;
  pushcli();
  c = mycpu();
  p = c->proc;
  popcli();
  return p;
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;

  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;

  release(&ptable.lock);

  // Allocate kernel stack.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;

  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;

  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;

  return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];

  p = allocproc();
  
  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  // this assignment to p->state lets other cores
  // run this process. the acquire forces the above
  // writes to be visible, and the lock is also needed
  // because the assignment might not be atomic.
  acquire(&ptable.lock);

  p->state = RUNNABLE;

  release(&ptable.lock);
  
  redist();
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *curproc = myproc();

  sz = curproc->sz;
  if(n > 0){
    if((sz = allocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  curproc->sz = sz;
  switchuvm(curproc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *curproc = myproc();
  
  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }

  // Copy process state from proc.
  if((np->pgdir = copyuvm(curproc->pgdir, curproc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = curproc->sz;
  np->parent = curproc;
  *np->tf = *curproc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);
  np->cwd = idup(curproc->cwd);

  safestrcpy(np->name, curproc->name, sizeof(curproc->name));

  pid = np->pid;

  acquire(&ptable.lock);
  np->state = RUNNABLE;
  release(&ptable.lock);

  if(child_bit == 1){
    // p->state = RUNNING;
    yield();
  }

  redist();
  //np = new process
  //curproc = caller
  // np->pass = 0;
  // np->stride = (total_tickets * 10) / (np->ticket);

  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curproc = myproc();
  struct proc *p;
  int fd;

  if(curproc == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd]){
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(curproc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.

  curproc->state = ZOMBIE;
  redist();
  sched();
  panic("zombie exit");
  
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;
  struct proc *curproc = myproc();
  
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curproc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        p->state = UNUSED;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || curproc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curproc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.

//Does this have to take an argument
void
scheduler(void)
{
  // cprintf("sched policy is %d\n\n\n", sched_policy);
  
  struct proc *p;
  struct cpu *c = mycpu();
  c->proc = 0;
  
  int ran = 0; // CS 350/550: to solve the 100%-CPU-utilization-when-idling problem

  for(;;){
    // Enable interrupts on this processor.
    sti();
    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
    ran = 0;
    if (sched_policy == 0){
      // cprintf('round robin time :)');
      //RR
      for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
        if(p->state != RUNNABLE)
          continue;
        ran = 1;
        // Switch to chosen process.  It is the process's job
        // to release ptable.lock and then reacquire it
        // before jumping back to us.
        c->proc = p;
        switchuvm(p);
        p->state = RUNNING;

        swtch(&(c->scheduler), p->context);
        switchkvm();

        // Process is done running for now.
        // It should have changed its p->state before coming back.
        c->proc = 0;
      }
    }else{
      // cprintf("stride schedule~ time :)");
      //TODO: Stride
      //Choose which process to run
      struct proc *highestProc = NULL;
      int lowestPassValue = -1; 
      for(struct proc *p = ptable.proc; p < &ptable.proc[NPROC]; p++){
        //iterates through proc table
        if (p->state != RUNNABLE){
          //skips over any process that's not runnable
          //Should running processes also qualify??
          continue;
        }
        if (highestProc == NULL && lowestPassValue == -1){
          //first iteration
          highestProc = p;
          lowestPassValue = p->pass;
          //p->pass should be set to 0 so this is 0
        }else{
          //compare priority
          //Shouldn't lowest pass value be a negative number since -1 is less than any whole number and i'm pretty sure pass should only
          //be a whole number p->pass will never be lower than lowestPassValue??
          //it takes care of that in the first loop nvm
          if (p->pass < lowestPassValue){// || ((p->pass == lowestPassValue) && (p->pid < highestProc->pid))){
            //Should there be parenthesis here? ^^^
            //doubler check
            
            highestProc = p;
            lowestPassValue = p->pass;
          }
        }
      }
      p = highestProc;
      //run the process
      if (p == NULL){
        ran = 0;
      }else{
        ran = 1;
        // Switch to chosen process.  It is the process's job
        // to release ptable.lock and then reacquire it
        // before jumping back to us.
        p->pass += p->stride;
        c->proc = p;
        switchuvm(p);
        p->state = RUNNING;

        swtch(&(c->scheduler), p->context);
        switchkvm();

        // Process is done running for now. --> change the pass value 
        
        // It should have changed its p->state before coming back.
        c->proc = 0;
      }
    }
    release(&ptable.lock);

    if (ran == 0){
        halt();
    }
  }
}

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->ncli, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();
  // cprintf("Process %d -> %d tickets | %d pass | %d stride", p->pid,p->ticket,p->pass,p->stride);

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = mycpu()->intena;
  swtch(&p->context, mycpu()->scheduler);
  mycpu()->intena = intena;
 
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  if (sched_trace_enabled)
  {
    cprintf("%d", myproc()->pid);
    
    sched_trace_counter++;
    if (sched_trace_counter % 20 == 0)
    {
      cprintf("\n");
    }
    else
    {
      cprintf(" - ");
    }
  }
    
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  if(p == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}

int
getproctickets(int pid)
{
  // cprintf("ooga booga");
  struct proc *p;
  int ticket = -1;


  // acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
    if(p->state == UNUSED)
      continue;
    if(p->pid == pid) {
      ticket = p->ticket;
      // release(&ptable.lock);
      return ticket;
    }
  }
  // release(&ptable.lock);
  return -1;
}

struct proc *
get_proc(int pid)
{
  // cprintf("ooga booga");
  struct proc *p;
  int ticket = -1;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
    if(p->state == UNUSED)
      continue;
    if(p->pid == pid) {
      ticket = p->ticket;
      // release(&ptable.lock);
      //put ticket transfer stuff here so ptable isn't an issue
      //no return either
      return p;
    }
  }
  release(&ptable.lock);
  return NULL;
}


int
transferTicketHelper(int recipientPID, int transferAmount)
{
  // cprintf("ooga booga");
  struct proc *p;
  int ticket = -1;
  struct proc * sender = myproc();
  //error handling
  if(transferAmount < 0){
    // release(&ptable.lock);
    return -1;
  }
  if(transferAmount > (sender->ticket - 1)){
    // release(&ptable.lock);
    return -2;
  }

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
    if(p->state == UNUSED) //I honestly forgot if this was a problem or not
      continue;
    if(p->pid == recipientPID) {
      ticket = p->ticket;
      sender->ticket -= transferAmount;
      p->ticket += transferAmount;

      sender->stride = (total_tickets * 10) / (sender -> ticket);
      p -> stride = (total_tickets * 10) / (p -> ticket);

      release(&ptable.lock);
      //put ticket transfer stuff here so ptable isn't an issue
      //no return either
      return transferAmount;
    }
  }
  release(&ptable.lock);
  return -3;
}



// //reset ticket and stride for both processes in getproc loop if it's equal to pid
// //then release
// int transferTicketHelper2(int recipientPID, int transferAmount){

//   // acquire(&ptable.lock);
//   if(transferAmount < 0){
//     // release(&ptable.lock);
//     return -1;
//   }
  
//   struct proc * sender = myproc();
//   struct proc * recipient = get_proc(recipientPID);
//   if(recipient == NULL){
//     // release(&ptable.lock);
//     return -3;
//   }
//   if(transferAmount > (sender->ticket - 1)){
//     // release(&ptable.lock);
//     return -2;
//   }

//   sender->ticket -= transferAmount;
//   recipient->ticket += recipient->ticket + transferAmount;
//   release(&ptable.lock);

//   /* TODO: potentially changing stride for both */
//   sender->stride = (total_tickets * 10) / (sender -> ticket);
//   recipient -> stride = (total_tickets * 10) / (recipient -> ticket);
//   return sender->ticket;
// }

int
redist()
{
    struct proc *p;
    struct proc *valid_table[NPROC];
    int num_tix;
    int table_ctr = 0;

    for (p = ptable.proc; p < &ptable.proc[NPROC]; p++) {
        if (p->state != RUNNING && p->state != RUNNABLE)
        //Running And Runnable
        //Shouldn't this be !Runnable just like in scheduler
            continue;
        if (table_ctr >= NPROC) {
            cprintf("redist: too many valid processes\n");
            //release(&ptable.lock);
            return -1;
        }
        valid_table[table_ctr] = p;
        table_ctr++;
    }

    if (table_ctr == 0) {
        cprintf("redist: no valid processes found\n");
        //release(&ptable.lock);
        return -1;
    }

    num_tix = 100 / table_ctr;
    // cprintf("\nACTIVE PROCS: %d\nNUM_TIX: %d\nTOTAL_TIX: %d\n",table_ctr,num_tix,total_tickets);

    total_tickets = num_tix * table_ctr;
    // cprintf("total tickets = %d", total_tickets);
    // cprintf("num_tix = %d", num_tix);
    for (int i = 0; i < table_ctr; i++) {
      //Should pass be set to 0 for the current ticket if it finished running 
      //Why are we calling p again here??
        p = valid_table[i];
        p->ticket = num_tix;
        p->stride = (total_tickets * 10) / p->ticket;
        p->pass = 0;

    }

    return 0;
}

/*
//returns pointer to highest priority process
struct proc *highestPriorityProcess(){
  struct proc *highestProc = NULL;
  int lowestPassValue = -1; 
  for(struct proc *p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if (p->state != RUNNABLE){
      continue;
    }
    if (highestProc == NULL && lowestPassValue == -1){
      highestProc = p;
      lowestPassValue = p->pass;
    }else{
      //compare priority
      if (p->pass < lowestPassValue || p->pass == lowestPassValue && p->pid < highestProc->pid){
        highestProc = p;
        lowestPassValue = p->pass;
      }
    }
  }
  return highestProc;
}
*/

