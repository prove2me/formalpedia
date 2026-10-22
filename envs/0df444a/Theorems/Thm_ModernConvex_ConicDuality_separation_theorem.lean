-- Prove2me | Theorems.Thm_ModernConvex_ConicDuality_separation_theorem
-- name    : ModernConvex.ConicDuality.separation_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:32.684261+00:00
-- url     : https://prove2.me/theorems/fa8c3674-3db6-452f-98dc-6a481e1a9855
-- title:
--   Theorem 2.4.2 — separation theorem for convex sets
-- statement:
--   Let $S, T$ be nonempty, nonintersecting convex subsets of $\mathbb R^m$. Then $S$ and $T$ can be separated by a linear functional: there exists a nonzero vector $\lambda \in \mathbb R^m$ such that
--   $$\sup_{u\in S}\lambda^Tu \le \inf_{u\in T}\lambda^Tu.$$
--
--   No openness, closedness or boundedness is assumed: in finite dimension two disjoint convex sets can always be separated (not necessarily strictly). The book uses this to separate a sublevel set of the primal objective from the interior of the cone in the proof of the conic duality theorem.
--
--   **Formalization Note** Vectors are `Fin m → ℝ`. The inequality between the supremum and the infimum is stated in the equivalent pointwise form $\lambda^Tu \le \lambda^Tv$ for all $u \in S$, $v \in T$ (both sets are nonempty, so neither side is a junk value).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 58, Theorem 2.4.2

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix

namespace ModernConvex.ConicDuality

/-- Ben-Tal–Nemirovski, Theorem 2.4.2 (separation theorem for convex sets), p. 58: nonempty,
nonintersecting convex sets `S, T ⊂ ℝᵐ` are separated by a nonzero linear functional:
`sup_{u∈S} λᵀu ≤ inf_{u∈T} λᵀu`, stated pointwise as `λᵀu ≤ λᵀv` for all `u ∈ S`, `v ∈ T`. -/
theorem separation_theorem {m : ℕ} (S T : Set (Fin m → ℝ)) (hS : S.Nonempty) (hT : T.Nonempty)
    (hSc : Convex ℝ S) (hTc : Convex ℝ T) (hST : Disjoint S T) :
    ∃ l : Fin m → ℝ, l ≠ 0 ∧ ∀ u ∈ S, ∀ v ∈ T, l ⬝ᵥ u ≤ l ⬝ᵥ v := by sorry

end ModernConvex.ConicDuality
