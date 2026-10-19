-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_Heat_finite_variance_bounds
-- name    : OAI.TriangularHilbert.Heat.finite_variance_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:52:27.179568+00:00
-- url     : https://prove2.me/theorems/6df37f2f-4bbb-486e-b751-e7e7ba59b278
-- title:
--   Positive variances lie in a compact positive range
-- statement:
--   For any three variances $\sigma_0,\sigma_1,\sigma_2>0$ there are constants $0<a\le b$ with
--   $$
--   a\le\sigma_w\le b\qquad(w=0,1,2).
--   $$
--
--   This trivial compactness lets uniform bounds that require variances in a compact interval $[a,b]\subset(0,\infty)$ be applied at any fixed positive variances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/PlaneIntegral.lean#L54-L66

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
universe uι
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

theorem OAI.TriangularHilbert.Heat.finite_variance_bounds (σ : Three → ℝ) (hσ : ∀ w, 0 < σ w) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ (∀ w, a ≤ σ w) ∧ (∀ w, σ w ≤ b) := by sorry
