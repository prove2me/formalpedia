-- Prove2me | Theorems.Thm_OAI_RuledApproximation_finite_weighted_grid_outer
-- name    : OAI.RuledApproximation.finite_weighted_grid_outer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:43:39.863142+00:00
-- url     : https://prove2.me/theorems/e842f3c4-f175-4965-9097-1b41c83cc28f
-- title:
--   Finite lattice sets around a compact set whose Riemann-sum cost approximates the integral
-- statement:
--   Equip $\mathbb{R}^2$ with the maximum norm $\|x\|_\infty=\max(|x_1|,|x_2|)$ and with Lebesgue measure, and for a positive integer $n$ let $\Lambda_n=\tfrac1n\mathbb{Z}^2$ be the square lattice of mesh $1/n$. Let $K\subseteq U\subseteq\mathbb{R}^2$ with $K$ compact and $U$ open, let $F:\mathbb{R}^2\to\mathbb{R}$ be continuous with $F\ge0$, and let $R\in\mathbb{R}$ and $\varepsilon>0$. Then for all sufficiently large $n\in\mathbb{N}$ we have $n\ge1$, and there is a finite set $S\subseteq\mathbb{R}^2$ such that
--
--   1. $S\subseteq U\cap\Lambda_n$;
--   2. every lattice point $b\in\Lambda_n$ with $\|b-p\|_\infty\le R/n$ for some $p\in K$ belongs to $S$;
--   3. the normalized weighted count of $S$ nearly matches the integral of $F$ over $K$:
--   $$
--   \frac{1}{n^2}\sum_{b\in S}F(b)<\int_KF(p)\,dp+\varepsilon.
--   $$
--
--   In the covering construction the points of $S$ are the centres of the cylinders: item 2 guarantees that every lattice point needed to approximate a label in $K$ at scale $R/n$ is available, and item 3 controls the total cost by a Riemann sum. No regularity of the boundary of $K$ and no positivity of its area is assumed.
--
--   **Formalization Note** The lattice is `coordinateGrid n`, the set $n^{-1}\cdot\mathbb{Z}^2$ inside `Fin 2 → ℝ` (whose Mathlib norm is the sup norm); "for all sufficiently large $n$" is the filter statement `∀ᶠ n in atTop`, and the finite sum is written as a `tsum` over the finite set $S$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/OuterApproximation.lean#L80-L112

import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation

open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

theorem OAI.RuledApproximation.finite_weighted_grid_outer {K U : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {F : (Fin 2 → ℝ) → ℝ} (hF : Continuous F) (hFpos : ∀ x, 0 ≤ F x)
    (R : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∃ S : Set (Fin 2 → ℝ), S.Finite ∧
      S ⊆ U ∩ coordinateGrid n ∧
      (∀ b ∈ coordinateGrid n, (∃ p ∈ K, dist b p ≤ R / n) → b ∈ S) ∧
      (∑' b : S, F b) / (n : ℝ) ^ 2 < (∫ p in K, F p) + eps := by sorry
