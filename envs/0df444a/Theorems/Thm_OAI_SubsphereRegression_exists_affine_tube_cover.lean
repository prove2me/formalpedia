-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_exists_affine_tube_cover
-- name    : OAI.SubsphereRegression.exists_affine_tube_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:07:20.188622+00:00
-- url     : https://prove2.me/theorems/b2b36e53-a5d9-4589-ba3f-ef2ef875da4a
-- title:
--   Covering the unit-ball part of an affine tube by $(3/r)^{\dim L}$ balls of radius $2r$
-- statement:
--   Let $E$ be a finite-dimensional real inner product space (with its Borel $\sigma$-algebra) and let $L\subseteq E$ be a nonempty affine subspace with direction $\vec L$, the linear subspace of differences of points of $L$. Let $p_0=\pi_L(0)$ be the orthogonal projection of the origin onto $L$ (the point of $L$ closest to $0$), so that $L=p_0+\vec L$, and write $\operatorname{dist}(t,L)=\inf_{q\in L}\|t-q\|$. For every $0<r\le1$ there is a finite set $S\subseteq\vec L$ with
--   $$|S|\le\left(\frac{3}{r}\right)^{\dim\vec L}$$
--   such that every $t\in E$ with $\|t\|\le1$ and $\operatorname{dist}(t,L)\le r$ satisfies
--   $$\|t-(y+p_0)\|\le2r\qquad\text{for some }y\in S.$$
--   Thus the part of the closed $r$-neighbourhood of $L$ inside the closed unit ball is covered by at most $(3/r)^{\dim\vec L}$ closed balls of radius $2r$, centred at points $y+p_0$ of $L$.
--
--   The number of balls depends only on the dimension of $L$, not on that of $E$. The centres need not lie in the support of a given measure, which is why this covering is combined with the radius-doubling form of the local mass bound in the estimate of the mass of affine tubes.
--
--   **Formalization Note** $\pi_L$ is `EuclideanGeometry.orthogonalProjection L`, the set $S$ is a `Finset L.direction`, and $\operatorname{dist}(t,L)$ is `Metric.infDist t L`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Geometry.lean#L265-L297

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open EuclideanGeometry

theorem OAI.SubsphereRegression.exists_affine_tube_cover (L : AffineSubspace ℝ E) [Nonempty L]
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset L.direction,
      (s.card : ℝ) ≤ (3 / r) ^ Module.finrank ℝ L.direction ∧
      ∀ t : E, ‖t‖ ≤ 1 → Metric.infDist t L ≤ r →
        ∃ y ∈ s, dist t ((y : E) + (orthogonalProjection L 0 : E)) ≤ 2 * r := by sorry
