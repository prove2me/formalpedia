-- Prove2me | Theorems.Thm_NatureSLT_Margin_margin_vc_dim_bound
-- name    : NatureSLT.Margin.margin_vc_dim_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:57.603673+00:00
-- url     : https://prove2.me/theorems/e9794310-8ed6-4e2e-bc55-be28d5188f55
-- title:
--   Theorem 5.1 — the Δ-margin separating hyperplanes on a sphere of radius R have VC dimension h ≤ min([R²/Δ²], n) + 1
-- statement:
--   Let the vectors $x \in X \subseteq \mathbb R^n$ belong to a sphere of radius $R > 0$, and let $\Delta > 0$. A $\Delta$-margin separating hyperplane is a hyperplane $(w^* \cdot x) - b = 0$ with $|w^*| = 1$ that classifies $x$ as $y = 1$ if $(w^* \cdot x) - b \ge \Delta$ and as $y = -1$ if $(w^* \cdot x) - b \le -\Delta$. Its VC dimension on $X$ is the largest number $h$ of vectors of $X$ that can be labeled in all $2^h$ ways, each labeling realized by a $\Delta$-margin separating hyperplane that classifies every one of the $h$ vectors (none in the strip $|(w^* \cdot x) - b| < \Delta$). **Theorem 5.1** states that this VC dimension is bounded by the inequality
--
--   $$h \le \min\left(\left[\frac{R^2}{\Delta^2}\right], n\right) + 1,$$
--
--   where $[a]$ is the integer part of $a$ and $n$ is the dimension of the space.
--
--   The VC dimension of all separating hyperplanes in $\mathbb R^n$ is $n + 1$; the theorem says that requiring a margin $\Delta$ on data of radius $R$ can make the capacity much smaller, independently of $n$. This is the capacity control behind the optimal separating hyperplane and the support vector machine in high-dimensional feature spaces.
--
--   **Formalization Note** "Sphere of radius $R$" is the closed ball of radius $R$ about an arbitrary center; with the bias $b$ free the class is translation invariant. The VC dimension takes values in $\mathbb N \cup \{\infty\}$, so the inequality also excludes an infinite VC dimension. The integer part is the natural-number floor of the positive real $R^2/\Delta^2$. As printed, the bound is false (F4 in the mission's findings; checked in Lean): the vertices of an equilateral triangle inscribed in the unit circle of $\mathbb R^2$ are shattered with $\Delta = 3/4$, while $\min([16/9], 2) + 1 = 2$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, pp. 132–133, Theorem 5.1

import Mathlib
import Definitions.Def_NatureSLT_Margin_marginVCDim

namespace NatureSLT.Margin

/-- **Theorem 5.1** (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., pp. 132–133):
let the vectors `x ∈ X` belong to a sphere of radius `R`. Then the set of Δ-margin separating
hyperplanes has VC dimension `h` bounded by the inequality
`h ≤ min([R²/Δ²], n) + 1`,
where `[a]` is the integer part (p. 98) and `n` the dimension of the space.

"Sphere of radius `R`" is the closed ball of radius `R` about an arbitrary center `c`; `R > 0`
and `Δ > 0`. The VC dimension is `ℕ∞`-valued (`marginVCDim`), so the statement also excludes an
infinite VC dimension. -/
theorem margin_vc_dim_bound {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n)) (R Δ : ℝ) (hR : 0 < R) (hΔ : 0 < Δ)
    (hX : X ⊆ Metric.closedBall c R) :
    marginVCDim X Δ ≤ ((min ⌊R ^ 2 / Δ ^ 2⌋₊ n + 1 : ℕ) : ℕ∞) := by sorry

end NatureSLT.Margin
