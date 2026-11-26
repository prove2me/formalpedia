-- Prove2me | Theorems.Thm_LefebvreVariations_lonely_runner_tao_inductive_core
-- name    : LefebvreVariations.lonely_runner_tao_inductive_core
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T01:03:16.278818+00:00
-- url     : https://prove2.me/theorems/54b535e0-3c1f-4bb6-930c-fb4614e21807
-- title:
--   Lefebvre's variations, No. 135 — on a theme by Rosenfeld: Tao's finite checking for the lonely runner, the inductive step
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   For a real $x$ write $\|x\|$ for its distance to the nearest integer, and say that $\mathrm{LRC}(m)$ holds if every set of $m$ distinct positive integers has a $t$ with $\|tv\|\ge \frac1{m+1}$ for all its elements.
--
--   There is an absolute constant $C>0$ such that for every $n\ge1$: if $\mathrm{LRC}(m)$ holds for all $m<n$, and every $n$ distinct positive integers $v_1,\dots,v_n$ with $v_i\le n^{Cn^2}$ admit $t$ with $\|tv_i\|\ge\frac1{n+1}$ for all $i$, then $\mathrm{LRC}(n)$ holds.
--
--   This is the inductive form of Tao's finite-checking theorem (Theorem 1.3): a minimal counterexample to the lonely runner conjecture can be taken with speeds of size at most $n^{Cn^2}$. Here the hypothesis that all smaller cases hold is granted, which the minimal-counterexample argument allows.
--
--   **Formalization Note** The speeds are `v : Fin n → ℕ`, positive and injective, and the bound is `(v i : ℝ) ≤ n ^ (C * n ^ 2)` with a real exponent, exactly as in `LonelyRunnerConjecture.tao_finite_checking`. `LRC m` is `LonelyRunnerConjecture.LRC m` (for `m = 0` it is trivial).
--
--   **Why this is a Lefebvre variation.** It is the missing step of a Lean-verified reduction of the open statement `LonelyRunnerConjecture.tao_finite_checking` (Tao's finite-checking theorem: speeds up to $n^{Cn^2}$ suffice). The Lean-verified reduction proves the base statement from this one by strong induction, with nothing else open. This statement is the inductive core: given the conjecture for fewer runners, it is enough to check injective speed vectors bounded by $n^{Cn^2}$. It is the form in which the base statement is used, so it is close to a restatement of the base statement's content and should be read as a thin variation.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). T. Tao, Some remarks on the lonely runner conjecture, Contrib. Discrete Math. 13 (2018), Theorem 1.3 (equivalence of delta_n = 1/(n+1) for n ≤ n0 with the bounded-speed check). The statement here is the step (ii) ⇒ (i) of that theorem, applied to a minimal counterexample; it follows from Tao's theorem, so it is true if that theorem is. Citation from memory (no network). Origin of this statement: it is the missing step of a reduction of `LonelyRunnerConjecture.tao_finite_checking`. The file `lonely_runner_tao_inductive_core_reduction.lean` proves that platform theorem from it: the direction (i) ⇒ (ii) is elementary (Finset.image of an injective vector) and (ii) ⇒ (i) is strong induction on n using this statement. Caveat: this statement is close to the target (it removes only the trivial direction and the induction), so it is a thin variation.

import Definitions.Def_LonelyRunnerConjecture_Defs

set_option autoImplicit false

namespace LefebvreVariations
theorem lonely_runner_tao_inductive_core :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (∀ m : ℕ, m < n → LonelyRunnerConjecture.LRC m) →
      (∀ v : Fin n → ℕ, (∀ i, 0 < v i) → Function.Injective v →
        (∀ i, (v i : ℝ) ≤ (n : ℝ) ^ (C * (n : ℝ) ^ 2)) →
        ∃ t : ℝ, ∀ i, (1 : ℝ) / (n + 1 : ℝ) ≤
          LonelyRunnerConjecture.distToNearestInt (t * (v i : ℝ))) →
      LonelyRunnerConjecture.LRC n := by sorry
end LefebvreVariations
