#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include <stddef.h>
#include <stdbool.h>

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
} ptable;

struct rb_tree {
  struct spinlock lock;
  struct proc* min_vruntime;
  struct proc* root;
  int total_weight;
  int period;
  int count;
};

struct rb_tree rbtree;
int min_granularity = 2;

static struct proc *initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
  initlock(&rbtree.lock, "rbtree");
  rbtree.min_vruntime = NULL;
  rbtree.period = NPROC / 2;
  rbtree.total_weight = 0;
  rbtree.root = NULL;
  rbtree.count = 0;
}

void rb_rightrotate(struct proc* x) // ketab
{
    struct proc* left = x->left;
    x->left = left->right;
    if (x->left)
        x->left->parent = x;
    left->parent = x->parent;
    if (!x->parent)
        rbtree.root = left;
    else if (x == x->parent->left)
        x->parent->left = left;
    else
        x->parent->right = left;
    left->right = x;
    x->parent = left;
}
 
void rb_leftrotate(struct proc* x) //ketab
{
    struct proc* y = x->right;

    x->right = y->left;
    if (x->right)
        x->right->parent = x;

    y->parent = x->parent;
    if (!x->parent)
        rbtree.root = y;
    else if (x == x->parent->left)
        x->parent->left = y;
    else
        x->parent->right = y;

    y->left = x;
    x->parent = y;
}

void rb_insert_fix(struct proc* z)
{
    struct proc* parent_z = NULL;
    struct proc* grand_parent_z = NULL;
    struct proc* uncle = NULL;
    bool uncle_l=false;
    bool uncle_r=false;
    
    if(rbtree.root==z){
      z->color=BLACK;
    }
    else {
      while(z->parent->color!=BLACK && z->color==RED && z!=rbtree.root){
        parent_z = z->parent;
        grand_parent_z = z->parent->parent;
        // uncle black | null
        if(parent_z == grand_parent_z->left){
          uncle= grand_parent_z->right;
          uncle_r=true;
          uncle_l=false;
        }
        else{
          uncle = grand_parent_z->left;
          uncle_l=true;
          uncle_r=false;
        }


        if(uncle!=NULL && uncle->color==RED){

          // grand_parent_z->color = RED;
          parent_z->color = BLACK;
          uncle->color = BLACK;
          if(grand_parent_z!=rbtree.root){
            grand_parent_z->color = RED;
            // inja ba gg fargh
          }
           z = grand_parent_z;
        }
        else{

            if(uncle_r && z==z->parent->right){   //      0    va kolan chap
                                                    // 0     
                                                        //0
              rb_leftrotate(parent_z);
              z = parent_z;
              parent_z = z->parent;
            }
            if(uncle_r && z==z->parent->left){   //   0
                                                  //0
                                                //0

              rb_rightrotate(grand_parent_z);
              int t = parent_z->color;
              parent_z->color = grand_parent_z->color;
              grand_parent_z->color = t;
              z = parent_z;
              
            }
            if(uncle_l && z==z->parent->right){  //0
                                                    //0
                                                      //0

              rb_leftrotate(grand_parent_z);
              int t = parent_z->color;
              parent_z->color = grand_parent_z->color;
              grand_parent_z->color = t;
              z = parent_z;

              
            }
            if(uncle_l && z==z->parent->left){ //0
                                                  //0
                                                //0

              rb_rightrotate(parent_z);
              z = parent_z;
              parent_z = z->parent;
              
            }
        }

      }
    }
}

void rb_insert(struct proc* z) 
{
  acquire(&rbtree.lock);

  if(rbtree.count == NPROC)
  {
    release(&rbtree.lock);
    return;
  }

  struct proc* y = NULL;
  struct proc* x = rbtree.root;
  z->color =  RED;

  while (x != NULL) {
    y = x;

    if (z->vruntime < x->vruntime)
      x = x->left;
    else
      x = x->right;
  }

  z->parent = y;

  if (y == NULL)
    rbtree.root = z; // khali bude

  else if (z->vruntime < y->vruntime)
    y->left = z;
  else
    y->right = z;

  if(rbtree.count == 0)
    rbtree.root->parent = NULL;

  rbtree.count ++;
  
  //Calculate weight
  z->weight = (int) (1024 / pow(1.25, z->nice));
  rbtree.total_weight += z->weight;

  rb_insert_fix(z);

  if(rbtree.min_vruntime == 0 || rbtree.min_vruntime->left != NULL)
		rbtree.min_vruntime = rb_min(rbtree.root);

  release(&rbtree.lock);
}

struct proc* rb_min(struct proc* x) //to shkehaye x min vruntime peyda
{
  struct proc* y= NULL;
  while(x!=NULL){
    y=x;
    x=x->left;
  }
  return y;

};

struct  proc* rb_select(struct proc* x)
{
  struct proc* temp = rbtree.root;
  while(temp!=NULL && temp->pid!=x->pid){
    if(x->vruntime>temp->vruntime){
      temp=temp->right;
    }
    else{
      temp=temp->left;
    }
  }
  return temp;
};

void rb_transplant(struct proc* u, struct proc* v){
  if(u->parent==NULL){
    rbtree.root=v;
  }
  else if(u==u->parent->left){
    u->parent->left=v;
  }
  else{
    u->parent->right=v;
  }
  v->parent=u->parent;
}

void rb_delete_fix(struct proc* x){ //baraye in baksh az ketab estefade
  struct proc* sibling=NULL;
  while (x != rbtree.root && x->color == BLACK){
    if(x==x->parent->left){
      sibling=x->parent->right;

      if(sibling->color==RED){
        sibling->color=BLACK;
        x->parent->color=RED;
        rb_leftrotate(x->parent);
        sibling=x->parent->right;
      }

      if(sibling->left->color==BLACK && sibling->right->color==BLACK){
        sibling->color=RED;
        x=x->parent;
      }

      else {
        if(sibling->right->color==BLACK){
          sibling->left->color=BLACK;
          sibling->color=RED;
          rb_rightrotate(sibling);
          sibling=x->parent->right;

        }
        
        sibling->color=x->parent->color;
        x->parent->color=BLACK;
        sibling->right->color=BLACK;
        rb_leftrotate(x->parent);
        x=rbtree.root;
      }


    }
    else{
      sibling=x->parent->left;

      if(sibling->color==RED){
        sibling->color=BLACK;
        x->parent->color=RED;
        rb_rightrotate(x->parent);
        sibling=x->parent->left;
      }

      if(sibling->right->color==BLACK && sibling->left->color==BLACK){
        sibling->color=RED;
        x=x->parent;
      }

      else {
        if(sibling->left->color==BLACK){
          sibling->right->color=BLACK;
          sibling->color=RED;
          rb_leftrotate(sibling);
          sibling=x->parent->left;

        }
        
        sibling->color=x->parent->color;
        x->parent->color=BLACK;
        sibling->left->color=BLACK;
        rb_rightrotate(x->parent);
        x=rbtree.root;
      }
    }
  }

  x->color=BLACK;
  
}

void rb_delete(struct proc* a) //baraye in baksh az ketab estefade
{
  acquire(&rbtree.lock);
  
  if(rbtree.count == 0)
  {
    release(&rbtree.lock);
    return;
  }
  else
  {
    struct proc* x;
    struct proc*z=a;

    if(z==NULL){
      //not found
    }
    struct proc* y=z;
    enum Color o_color=y->color; // rang proc ke hazf

    if(z->left==NULL){
      x=z->right;
      rb_transplant(z,x);
    }
    else if(z->right==NULL){
      x=z->left;
      rb_transplant(z,x);
    }
    else{
      y=rb_min(z->right);
      o_color=y->color;
      x=y->right;
      if(y->parent==z){
        x->parent=y;
      }
      else{
        rb_transplant(y,y->right);
        y->right=z->right;
        y->right->parent=y;
      }
      rb_transplant(z,y);
      y->left=z->left;
      y->left->parent=y;
      y->color=z->color;
    }
    if(o_color==BLACK){
      rb_delete_fix(x);
    }
  }
  if(((NPROC / 2) / min_granularity) < rbtree.count)
    rbtree.period = min_granularity * rbtree.count;

  rbtree.count --;
  a->time_slice = (a->weight * rbtree.period) / rbtree.total_weight;
  rbtree.total_weight -= a->weight;
  rbtree.min_vruntime = rb_min(rbtree.root);
  release(&rbtree.lock);
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

  rb_insert(p);
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

  rb_insert(np);

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
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();
  c->proc = 0;
  
  for(;;){
    // Enable interrupts on this processor.
    sti();

    p = rbtree.min_vruntime;

    while(p != NULL){
      rb_delete(p);
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
      p = rbtree.min_vruntime;
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
  //interrupt dige nakhore
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
  rb_insert(myproc());
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
    {
      p->state = RUNNABLE;
      rb_insert(p);
    }
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
      {
        p->state = RUNNABLE;
        rb_insert(p);
      }
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