import GlimpseOfLean.Library.Basic
open Set

namespace ClassicalPropositionalLogic

/- Let's try to implement a language of classical propositional logic.

Note that there is also version of this file for intuitionistic logic:
`IntuitionisticPropositionalLogic.lean`
-/

def Variable : Type := ℕ

/- We define propositional formula, and some notation for them. -/

inductive Formula : Type where
  | var : Variable → Formula
  | bot : Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula

open Formula
local notation:max (priority := high) "#" x:max => var x
local infix:30 (priority := high) " || " => disj
local infix:35 (priority := high) " && " => conj
local infix:28 (priority := high) " ⇒ " => impl
local notation (priority := high) "⊥" => bot

def neg (A : Formula) : Formula := A ⇒ ⊥
local notation:(max+2) (priority := high) "~" x:max => neg x
def top : Formula := ~⊥
local notation (priority := high) "⊤" => top
def equiv (A B : Formula) : Formula := (A ⇒ B) && (B ⇒ A)
local infix:29 (priority := high) " ⇔ " => equiv

/- Let's define truth w.r.t. a valuation, i.e. classical validity -/

@[simp] --TODO mention in the doc that function also can be declated with simp
def IsTrue (v : Variable → Prop) : Formula → Prop
  | ⊥      => False
  | # P    => v P
  | A || B => IsTrue v A ∨ IsTrue v B
  | A && B => IsTrue v A ∧ IsTrue v B
  | A ⇒ B => IsTrue v A → IsTrue v B

def Satisfies (v : Variable → Prop) (Γ : Set Formula) : Prop := ∀ {A}, A ∈ Γ → IsTrue v A
def Models (Γ : Set Formula) (A : Formula) : Prop := ∀ {v}, Satisfies v Γ → IsTrue v A
local infix:27 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A

/- Here are some basic properties of validity.

  The tactic `simp` will automatically simplify definitions tagged with `@[simp]` and rewrite
  using theorems tagged with `@[simp]`. -/

variable {v : Variable → Prop} {A B : Formula}
@[simp] lemma isTrue_neg : IsTrue v ~A ↔ ¬ IsTrue v A := by simp

@[simp] lemma isTrue_top : IsTrue v ⊤ := by {
  simp
}

@[simp] lemma isTrue_equiv : IsTrue v (A ⇔ B) ↔ (IsTrue v A ↔ IsTrue v B) := by {
  simp
  tauto
}

/- As an exercise, let's prove (using classical logic) the double negation elimination principle.
  `by_contra h` might be useful to prove something by contradiction. -/

example : Valid (~~A ⇔ A) := by {
  unfold Valid
  unfold Models
  intro v h
  simp
}

example (h : p ∨ q) : q ∨ p := by
  cases h
  case inl hp => exact Or.inr hp
  case inr hq => exact Or.inl hq

@[simp] lemma satisfies_insert_iff : Satisfies v (insert A Γ) ↔ IsTrue v A ∧ Satisfies v Γ := by {
  simp [Satisfies] --TODO what is it mean
}

/- Let's define provability w.r.t. classical logic. -/
section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom

/- `Γ ⊢ A` is the predicate that there is a proof tree with conclusion `A` with assumptions from
  `Γ`. This is a typical list of rules for natural deduction with classical logic. -/
inductive ProvableFrom : Set Formula → Formula → Prop
  | ax    : ∀ {Γ A},   A ∈ Γ   → Γ ⊢ A
  | impI  : ∀ {Γ A B},  insert A Γ ⊢ B                → Γ ⊢ A ⇒ B
  | impE  : ∀ {Γ A B},           Γ ⊢ (A ⇒ B) → Γ ⊢ A  → Γ ⊢ B
  | andI  : ∀ {Γ A B},           Γ ⊢ A       → Γ ⊢ B  → Γ ⊢ A && B
  | andE1 : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ A
  | andE2 : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ B
  | orI1  : ∀ {Γ A B},           Γ ⊢ A                → Γ ⊢ A || B
  | orI2  : ∀ {Γ A B},           Γ ⊢ B                → Γ ⊢ A || B
  | orE   : ∀ {Γ A B C}, Γ ⊢ A || B → insert A Γ ⊢ C → insert B Γ ⊢ C → Γ ⊢ C
  | botC  : ∀ {Γ A},   insert ~A Γ ⊢ ⊥                → Γ ⊢ A

end

local infix:27 (priority := high) " ⊢ " => ProvableFrom

/- A formula is provable if there is a -/
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE botC andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}

/- We define a simple tactic `apply_ax` to prove something using the `ax` rule. -/
syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) =>
    `(tactic| first | apply mem_insert | apply mem_insert_of_mem; solve_mem
                    | fail "tactic \'apply_ax\' failed")
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })

/- To practice with the proof system, let's prove the following.
  You can either use the `apply_ax` tactic defined on the previous lines, which proves a goal that
  is provable using the `ax` rule.
  Or you can do it manually, using the following lemmas about insert.
```
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
```
-/

example : insert A (insert B ∅) ⊢ A && B := by
  exact andI (ax (mem_insert _ _)) (ax (mem_insert_of_mem _ (mem_insert _ _)))

example : insert A (insert B ∅) ⊢ A && B := by
  exact andI (by apply_ax) (by apply_ax)

example : Provable (~~A ⇔ A) := by {
  unfold Provable
  unfold equiv
  unfold neg
  apply andI


  apply impI
  apply botC
  apply @impE _ (A ⇒ ⊥) --TODO how to use "apply with" of coq here?
  apply_ax
  apply_ax


  apply impI
  apply impI
  apply impE
  apply_ax
  apply_ax
}

/- Optional exercise: prove the law of excluded middle. -/
example : Provable (A || ~A) := by {
  unfold Provable
  unfold neg

  --botC is same as ~~A = A

  apply botC
  apply impE
  apply_ax
  apply orI2
  apply impI
  apply impE
  apply_ax
  apply orI1
  apply_ax
}

/- Optional exercise: prove one of the de-Morgan laws.
  If you want to say that the argument called `A` of the axiom `impE` should be `X && Y`,
  you can do this using `impE (A := X && Y)` -/
example : Provable (~(A && B) ⇔ ~A || ~B) := by {
  unfold Provable
  unfold equiv
  unfold neg


  apply andI
  apply impI
  apply botC
  apply impE
  apply ax
  apply mem_insert_of_mem
  apply mem_insert
  apply andI

  apply botC
  apply impE
  apply ax
  apply mem_insert_of_mem
  apply mem_insert
  apply orI1
  apply_ax

  apply botC
  apply impE
  apply ax
  apply mem_insert_of_mem
  apply mem_insert
  apply orI2
  apply_ax

  apply impI
  apply impI
  apply orE
  apply_ax
  apply impE
  apply_ax
  apply andE1
  apply_ax
  apply impE
  apply_ax
  apply andE2
  apply_ax
}

/- You can prove the following using `induction` on `h`. You will want to tell Lean that you want
  to prove it for all `Δ` simultaneously using `induction h generalizing Δ`.
  Lean will mark created assumptions as inaccessible (marked with †)
  if you don't explicitly name them.
  You can name the last inaccessible variables using for example `rename_i ih` or
  `rename_i A B h ih`. Or you can prove a particular case using `case impI ih => <proof>`.
  You will probably need to use the lemma
  `insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t`. -/
lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by {
  induction h generalizing Δ

  apply ax
  apply h2 (by assumption)

  apply impI
  apply insert_subset_insert at h2
  rename_i h
  apply h h2

  apply impE
  rename_i h _
  apply h (by assumption)
  rename_i h
  apply h (by assumption)

  apply andI
  rename_i h _
  apply h (by assumption)
  rename_i h
  apply h (by assumption)

  apply andE1
  rename_i h
  apply h h2

  apply andE2
  rename_i h
  apply h h2

  apply orI1
  rename_i h
  apply h (by assumption)

  apply orI2
  rename_i h
  apply h (by assumption)

  apply orE
  rename_i h _ _
  apply h (by assumption)
  rename_i h _
  apply h
  apply insert_subset_insert (by assumption)
  rename_i h
  apply h
  apply insert_subset_insert (by assumption)

  apply botC
  rename_i h
  apply h
  apply insert_subset_insert (by assumption)
}

/- Use the `apply?` tactic to find the lemma that states `Γ ⊆ insert x Γ`.
  You can click the blue suggestion in the right panel to automatically apply the suggestion. -/

lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by {
  apply weakening (by assumption)
  exact subset_insert B Γ
}

/- Proving the deduction theorem is now easy. -/
lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by {
   apply impE
   apply_ax
   apply h.insert --same as "apply ProvableFrom.insert h"
   --TODO add into notes
}

lemma Provable.mp (h1 : Provable (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by {
  unfold Provable at *
  apply impE
  apply impI
  apply deduction_theorem
  apply h2
  apply weakening
  apply h1
  exact empty_subset _
}

/-- You will want to use the tactics `left` and `right` to prove a disjunction, and the
  tactic `cases h` if `h` is a disjunction to do a case distinction. -/
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by {
  unfold Models
  unfold Satisfies
  intros v hv
  induction h
  case ax ih => apply hv; assumption
  case impI ih => intro ht; apply ih; intro a aΓ; cases' eq_or_mem_of_mem_insert aΓ with ha aΓ; rw [ha]; assumption; apply hv aΓ
  case impE ih1 ih2 => apply ih1 hv; apply ih2 hv
  case andI ih1 ih2 => apply And.intro; apply ih1 hv; apply ih2 hv
  case andE1 ih => cases ih hv; assumption
  case andE2 ih => cases ih hv; assumption
  case orI1 ih => apply Or.inl; apply ih hv
  case orI2 ih => apply Or.inr; apply ih hv
  case orE ih1 ih2 ih3 => cases' ih1 hv with ha hb; apply ih2; intro a aΓ; cases' eq_or_mem_of_mem_insert aΓ with ha aΓ; rw [ha]; assumption; apply hv aΓ; apply ih3; intro a aΓ; cases' eq_or_mem_of_mem_insert aΓ with ha aΓ; rw [ha]; assumption; apply hv aΓ;
  case botC ih => dsimp at *; by_contra; apply ih; intro a aΓ; cases' eq_or_mem_of_mem_insert aΓ with ha aΓ; rw [ha]; dsimp; assumption; apply hv aΓ
}

theorem valid_of_provable (h : Provable A) : Valid A := by {
  unfold Provable at *
  unfold Valid at *
  apply soundness_theorem
  assumption
}

/-
  TODO finish these two exercises

  If you want, you can now try some these longer projects.

  1. Prove completeness: if a formula is valid, then it is provable
  Here is one possible strategy for this proof:
  * If a formula is valid, then so is its negation normal form (NNF);
  * If a formula in NNF is valid, then so is its conjunctive normal form (CNF);
  * If a formula in CNF is valid then it is syntactically valid:
      all its clauses contain both `A` and `¬ A` in it for some `A` (or contain `⊤`);
  * If a formula in CNF is syntactically valid, then its provable;
  * If the CNF of a formula in NNF is provable, then so is the formula itself.
  * If the NNF of a formula is provable, then so is the formula itself.

  2. Define Gentzen's sequent calculus for propositional logic, and prove that this gives rise
  to the same provability.
-/

end ClassicalPropositionalLogic
