import data.set
open classical
open list
universes u v

variables P r: Prop


constant s : ℕ × ℕ
#check nat
-- cartesian product of two sets in the same universe maps to the same universe?
#check nat × nat
#check Type 
#check Type 1
#check Type × Type
-- this will map to Type 2, maps to highest hierarchy of type
#check Type 2 × Type 1
#check Type u
#check Type → Type
#check Type → Type → Type
#check list
#check list (Type 1)
#check (Type 1) × (Type 2)
#check fun x : nat, 5
constants α β γ : Type 
constant h : α → β → γ
-- comma indicates such that (part of an expression, space serves purpose of comma(except for in function evaluation?))
#check λ (x y), h x y
#check λ (α β : Type* ) (a : α) (b : β), a
constant a : α
#reduce (λ x : α, x) a


constant g : β → γ
constant f : α → β
#reduce (λ (v : β → γ) (u : α → β) x, v (u x)) g f a   -- γ
def compose (α β γ : Type*) (g : β → γ) (f : α → β) (x : α) :
  γ :=
g (f x)
#check compose

def double : ℕ → ℕ := λ x, x + x
def square : ℕ → ℕ := λ x, x * x
def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)

def quadruple := λ x, do_twice double x
#eval quadruple 3

def curry (α β γ : Type*) (f : α × β → γ) : α → β → γ := λ a b, f (a, b)
#check curry
def uncurry (α β γ : Type*) (f : α → β → γ) : α × β → γ := λ (c : α × β), f c.1 c.2 
#check uncurry
constant l : Type 1 → Type 1
#check l

def foo := let a := nat in λ x : a, x + 2

-- below fails bc, the expression (λ a, λ x : a, x + 2) cannot be type inferenced in isolation
/-
def bar := (λ a, λ x : a, x + 2) nat
-/

-- variable redeclared across sections
section asb 
variable (x : α)
def foo_asb := x
end asb

section asb1
variable (x : α)
def foo_asb1 := x
end asb1

#check list
#check @list.cons

constant vec : Type u → ℕ → Type u

namespace vec
constant empty : Π α : Type u, vec α 0
constant cons :
  Π (α : Type u) (n : ℕ), α → vec α n → vec α (n + 1)
constant append :
  Π (α : Type u) (n m : ℕ),  vec α m → vec α n → vec α (n + m)
-- vec add takes two vectors and adds their 
constant vec_add : Π (α : Type u ) (n : ℕ), vec α n → vec α n → vec α n
end vec

constant matrix : Type u → ℕ → ℕ → Type u
namespace matrix
-- takes and m (r) x n (c) matrix and an n (same number of columns) vector and returns an m vector
constant matrix_multiply : Π (α : Type u) (m : ℕ) (n : ℕ), matrix α m n → vec α n → vec α m
end matrix
namespace b
-- for each proposition $p$ we obtain a Type of proofs, there may be many proofs of P
constant Proof : Prop → Type

constant and : Prop → Prop → Prop
constant or : Prop → Prop → Prop
constant not : Prop → Prop
constant implies : Prop → Prop → Prop

-- the function is parametrized by p, q as the Types of Proofs is dependent upon the values of the propositions
def and_comm (p q : Prop) : Type :=
  Proof (implies (and p q) (and q p))

variables p q : Prop
#check and_comm p q      -- Proof (implies (and p q) (and q p))
#check and_comm
-- define and_comm in lambda notation
#check λ (p q : Prop), Proof (implies (and p q) (and p q))
constant modus_ponens : Π p q : Prop, implies p q → Proof p → Proof q
#check modus_ponens
end b

#check Prop
constant p : Prop
constant thm : p
#check p
#check thm

-- still a dependent type?
def compose_restricted_type (α β γ : Type) (g : β → γ) (f : α → β) (x : α) :
  γ :=
g (f x)
#check compose_restricted_type

-- below proof does not need to be bound to the variables defined above, can define analogously
variables p q : Prop
theorem t1 : p → q → p := λ hp : p, λ hq : q, hp

-- introduce p q as bound variables in definitions, as p q are bound this is equivalent to Π in function definition
theorem t2 (p q : Prop) : p → q → p := 
assume hp : p,
assume hq : q,
show p, from hp
#check t2

theorem t3 (p q r: Prop) (h₀ : p → q) (h₁ : q → r) (hp : p) : r := h₁ (h₀ hp)
#check t3

-- polymorphic over propositional arguments
#check @and.intro

example (p q : Prop) : p → q → p ∧ q :=
assume hp : p,
assume hq : q,
show p ∧ q, from and.intro hp hq

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := and.intro hp hq

#check @and.elim_left
#check @and.elim_right

example:  p ∧ q → q ∧ p :=
assume hpq : p ∧ q,
show q ∧ p, from and.intro hpq.right hpq.left

#check or.intro_right
#check @or.inr

theorem t5 : p ∨ q → q ∨ p :=
assume hpq : p ∨ q,
have hpr : p → q ∨ p := 
  assume hp : p,
  show q ∨ p, from or.intro_right q hp,
have hqr : q → q ∨ p := 
  assume hq : q,
  show q ∨ p, from or.intro_left p hq,
or.elim hpq hpr hqr
#check t5

#check ¬p
#check p → false

-- apply the fact that hnq : q → False to q
example (hpq : p → q) (hnq : ¬q): ¬p :=
assume hp : p,
show false, from false.elim (hnq (hpq hp))

#check @false.elim

#check @absurd

#check @iff.mp
#check @iff.mpr

theorem and_swap : p ∧ q ↔ q ∧ p :=
have hpq : p ∧ q → q ∧ p := assume hpq₀ : p ∧ q, and.intro hpq₀.right hpq₀.left,
-- two goals, 1. that and_swap follows from hqp, and hqp
suffices hqp : q ∧ p → p ∧ q, from iff.intro hpq hqp,
have hqp : q ∧ p → p ∧ q := sorry,
hqp


#check and_swap

#check classical.em

#check @by_cases

#check @classical.by_contradiction

example (p q : Prop) : (p → q) → (¬p → q) → q := 
assume hpq : p → q,
assume hnpq : ¬p → q,
or.elim (classical.em p)  hpq hnpq

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q := 
have hnp : ¬p → ¬p ∨ ¬q := assume hnp : ¬p, or.inl hnp,
have hp : p → ¬p ∨ ¬q := (
  assume hp : p,
  have hq : q → ¬p ∨ ¬q := (
    assume hq : q,
    absurd (and.intro hp hq) h
  ),
  have hnq : ¬q → ¬p ∨ ¬q := (
    assume hnq : ¬q,
    or.inr hnq
  ),
  -- use em q to derive that ¬q -> trivial, q -> absurd w/ h
  or.elim (classical.em q)  hq hnq
),
or.elim (classical.em p) hp hnp

theorem and_commutative : p ∧ q ↔ q ∧ p := 
iff.intro (
  assume hpq : p ∧ q,
  ⟨hpq.right , hpq.left⟩
)
(
  assume hqp : q ∧ p,
  ⟨hqp.right, hqp.left⟩
)

theorem or_commuatative : p ∨ q ↔ q ∨ p := 
have hpq : p ∨ q → q ∨ p := assume hpq : p ∨ q, or.elim hpq (assume hp : p, or.inr hp) (assume hq : q, or.inl hq),
have hqp : q ∨ p → p ∨ q := sorry,
iff.intro hpq hqp


