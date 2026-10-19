-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_finite_cost_dissipation
-- name    : OAI.TriangularHilbert.Heat.finite_cost_dissipation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:54:57.772801+00:00
-- url     : https://prove2.me/theorems/53c99657-3202-4aa3-b298-f49e042bdac0
-- title:
--   An algebraic dissipation inequality on the triangle
-- statement:
--   Let $\alpha_w\ge0$ for $w\in\{0,1,2\}$, let $K_{vw}\ge0$ and $Z_v$ be real numbers, and assume
--   $$
--   2Z_v\le\sum_{w\ne v}K_{vw}\quad\text{for all }v,\qquad\sum_{v\ne w}K_{vw}\le\sqrt2\,K_{ww}\quad\text{for all }w .
--   $$
--   Then
--   $$
--   \sum_v\Bigl(\Bigl(\sum_w\alpha_w\Bigr)Z_v-\sum_w\alpha_wK_{vw}\Bigr)\le\sum_w\Bigl(-\alpha_w+\sqrt2\max\Bigl(0,\frac{\sum_v\alpha_v}2-\alpha_w\Bigr)\Bigr)K_{ww} .
--   $$
--
--   This bookkeeping turns cross terms into a multiple of the diagonal Hessian costs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/DissipationAlgebra.lean#L10-L47

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MatrixEnergy
open scoped BigOperators

theorem OAI.TriangularHilbert.Heat.finite_cost_dissipation (α : Three → ℝ) (hα : ∀ w, 0 ≤ α w)
    (K : Three → Three → ℝ) (Z : Three → ℝ) (hK : ∀ v w, 0 ≤ K v w)
    (hrow : ∀ v, 2*Z v ≤ ∑ w, if w = v then 0 else K v w)
    (hcol : ∀ w, (∑ v, if v = w then 0 else K v w) ≤ Real.sqrt 2 * K w w) :
    (∑ v, ((∑ w, α w)*Z v - (∑ w, α w*K v w))) ≤
      ∑ w, (-α w + Real.sqrt 2 * max 0 ((∑ v, α v)/2-α w))*K w w := by sorry
