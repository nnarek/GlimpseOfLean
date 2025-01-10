import GlimpseOfLean.Library.Basic

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers.
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.
-/

/-
Before we start on, let us make sure Lean doesn't need so much help to
prove equalities or inequalities that linearly follow from known
equalities and inequalities. This is the job of the linear arithmetic
tactic: `linarith`.
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Let's prove some exercises using `linarith`.
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by {
  linarith
}

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by {
  linarith
}

/-
A sequence `u` is a function from `ℕ` to `ℝ`, hence Lean says
`u : ℕ → ℝ`
The definition we'll be using is:

-- Definition of « u tends to l »
`def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

Note the use of `∀ ε > 0, _` which is an abbreviation of
`∀ ε, ε > 0 → _ `

In particular, a statement like `h : ∀ ε > 0, _`
can be specialized to a given `ε₀` by
  `specialize h ε₀ hε₀`
where `hε₀` is a proof of `ε₀ > 0`.

Also note that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by`.
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.
-/

/- If u is constant with value l then u tends to l.
Hint: `simp` can rewrite `|l - l|` to `0` -/
example (h : ∀ n, u n = l) : seq_limit u l := by {
  unfold seq_limit
  intro ε hε
  use 1
  intros
  rw [h]
  simp
  linarith
}


/- When dealing with absolute values, we'll use lemmas:

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

We will also use variants of the triangle inequality

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
or
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
or the primed version:
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`
-/

-- Assume `l > 0`. Then `u` ts to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by {
  unfold seq_limit at *
  rcases h (l / 2) (by linarith) with ⟨N,hN⟩
  use N
  intro n nN
  specialize hN n nN
  rw [abs_le] at *
  linarith
}


/-
When dealing with max, you can use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

Let's see an example.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by {
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨_hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n (by linarith)

  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith [fact₁, fact₂]
}


/- Let's do something similar: the squeezing theorem. -/
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by {
  unfold seq_limit at *
  intro ε hε
  rcases hu ε hε with ⟨uN,huN⟩
  rcases hw ε hε with ⟨wN,hwN⟩
  use max uN wN
  intro n hn
  rw [ge_max_iff] at hn
  specialize huN n (by linarith)
  specialize hwN n (by linarith)
  rw [abs_le] at *
  specialize h n
  specialize h' n
  apply And.intro
  linarith
  linarith
}



/- In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

Recall we listed three variations on the triangle inequality at the beginning of this file.
-/

-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma uniq_limit : seq_limit u l → seq_limit u l' → l = l' := by {
  unfold seq_limit
  intros h h'
  apply eq_of_abs_sub_le_all
  intro ε hε
  rcases h (ε / 2) (by linarith) with ⟨N,hN⟩
  rcases h' (ε / 2) (by linarith) with ⟨N',hN'⟩
  specialize hN (max N N') (by apply le_max_left)
  specialize hN' (max N N') (by apply le_max_right)
  rw [abs_le] at *
  apply And.intro (by linarith) (by linarith)
}



/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by {
  unfold is_seq_sup at *
  unfold non_decreasing at *

  intro ε hε
  rcases h.right ε hε with ⟨N,hN⟩
  use N
  intro n hn
  rw [abs_le] at *
  apply And.intro

  specialize h' _ _ hn
  linarith

  rcases h with ⟨hl,_⟩
  specialize hl n
  linarith
}

/-
We will now play with subsequences.

The new definition we will use is that `φ : ℕ → ℕ` is an extraction
if it is (strictly) increasing.

`def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`

In the following, `φ` will always denote a function from `ℕ` to `ℕ`.

The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by {
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])
}


/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
-/

/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by {
  unfold extraction

  intro h N N'
  use max N N' + 1
  apply And.intro
  apply le_trans
  apply le_max_right N
  linarith

  apply le_trans
  apply id_le_extraction' h

  have aa : (N < max N N' + 1) := by apply Nat.lt_of_succ_le; apply Nat.succ_le_succ; apply le_max_left

  specialize h N (max N N' + 1) aa
  linarith
}

/- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`.

`def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a`
-/


/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by {
  unfold cluster_point
  unfold extraction
  unfold seq_limit
  unfold Function.comp

  intro ⟨φ,⟨ex,hl⟩⟩ ε hε N
  rcases hl ε hε with ⟨N',h⟩

  rcases lt_or_le N N' with hn | hn

  use φ N'
  specialize h N' (by linarith)
  apply And.intro
  apply le_trans
  apply id_le_extraction' ex
  specialize ex N N' hn
  linarith
  exact h

  use φ N
  specialize h N (by assumption)
  apply And.intro
  apply id_le_extraction' ex
  exact h
}


/-- If `u` tends to `l` then its subsequences tend to `l`. -/
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by {
  unfold extraction at *
  unfold seq_limit at *
  unfold Function.comp

  intro ε hε
  rcases h ε hε with ⟨N,h⟩
  use N
  intro n hn
  apply h (φ n)
  apply le_trans
  apply id_le_extraction' hφ
  rcases Nat.lt_or_eq_of_le hn with Neqn | Nlen
  apply hφ at Neqn
  linarith
  rw [Nlen]
}

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by {
  apply near_cluster at ha
  unfold seq_limit at *

  apply eq_of_abs_sub_le_all
  intro ε hε
  rcases hl (ε / 2) (by linarith) with ⟨N,h⟩
  specialize ha (ε / 2) (by linarith) N
  cases' ha with n hn
  specialize h n hn.left
  rw [abs_le] at *
  apply And.intro (by linarith) (by linarith)
}

/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by {
  unfold CauchySequence
  unfold seq_limit
  intros E ε hε
  cases' E with e he
  cases' he (ε / 2) (by linarith) with N hN
  use N
  intro p q hp hq
  have hp' := hN p hp
  have hq' := hN q hq
  rw [abs_le] at *
  apply And.intro (by linarith) (by linarith)
}

/-
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
  unfold CauchySequence at *
  unfold seq_limit at *

  apply near_cluster at hl
  intro ε hε
  cases' hu (ε / 2) (by linarith) with N hN
  cases' hl (ε / 2) (by linarith) N with n hn
  use N
  intro n' hn'
  specialize hN n n' hn.left hn'
  rw [abs_le] at *
  apply And.intro (by linarith) (by linarith)
