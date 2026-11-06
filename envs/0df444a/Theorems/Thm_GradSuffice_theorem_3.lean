-- Prove2me | Theorems.Thm_GradSuffice_theorem_3
-- name    : GradSuffice.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:22:40.126606+00:00
-- url     : https://prove2.me/theorems/9f07b085-3959-469e-b9e6-01c1f4a0781c
-- title:
--   Theorem 3, p.10 — $\mathcal R^{(s)}_m(B)>e\,m^{-1/q}$ yields a shattered tree of depth $\ge\exp(aq)$
-- statement:
--   Let $B$ be the unit ball of a real Banach space $X$.
--
--   **Theorem 3 (large sequential Rademacher complexity yields deep shattered trees).** There are universal constants $q_0\ge2$ and $a>0$ such that, for every $q\ge q_0$: if
--   $$\mathcal R^{(s)}_m(B)>e\,m^{-1/q}$$
--   for some integer $m\ge1$, then there is a $B^\star$-valued binary tree, shattered by $B$ at margin $1/10$, whose depth $n$ satisfies $n\ge\exp(aq)$.
--
--   By contraposition this is the implication 2 → 3 of Theorem 1: bounded shattered trees force polynomial decay of the sequential Rademacher complexity.
--
--   Differences from the source:
--   - encoding: R⁽ˢ⁾ₘ(B) > e m^{−1/q} (a supremum over adaptive sequences) → some B⋆-valued adaptive sequence ξ of length m has seqRad ξ > e m^{−1/q}; reason: a supremum exceeds a number iff some element does
--   - encoding: universal constants q₀, a → ∃ q₀ ≥ 2, a > 0 chosen before the space X; reason: quantifier form of "universal"
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 3, p.10

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_IsShattered
import Definitions.Def_GradSuffice_seqRad

namespace GradSuffice

/-- **Theorem 3 (large sequential Rademacher complexity yields deep shattered trees).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026,
Theorem 3, p.10: "There exist universal constants `q₀ ≥ 2` and `a > 0` such that the following holds.
Let `B` be the unit ball of a real Banach space, and fix `q ≥ q₀`. If `R⁽ˢ⁾ₘ(B) > e m^{−1/q}` for some
integer `m ≥ 1`, then there exists a `B⋆`-valued binary tree, shattered by `B` at margin `1/10`, whose
depth `n` satisfies `n ≥ exp(aq)`."

**Formalization Note.** `q₀` and `a` are chosen before the space. `R⁽ˢ⁾ₘ(B) > e m^{−1/q}` is
"some `B⋆`-valued adaptive sequence of length `m` has `R⁽ˢ⁾ₘ(B; ξ) > e m^{−1/q}`" (a supremum exceeds
a number iff some element does). -/
theorem theorem_3 :
    ∃ q₀ : ℝ, 2 ≤ q₀ ∧ ∃ a : ℝ, 0 < a ∧
      ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (q : ℝ), q₀ ≤ q →
      ∀ m : ℕ, 1 ≤ m →
        (∃ ξ : NondualOpt.Tree (StrongDual ℝ X) m, IsDualValued ξ ∧
          Real.exp 1 * (m : ℝ) ^ (-1 / q) < seqRad ξ) →
        ∃ (n : ℕ) (ζ : NondualOpt.Tree (StrongDual ℝ X) n), IsDualValued ζ ∧
          IsShattered (Metric.closedBall (0 : X) 1) (1 / 10) ζ ∧ Real.exp (a * q) ≤ n := by sorry

end GradSuffice
