-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_weighted_cubic
-- name    : OAI.TriangularHilbert.weighted_cubic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:06:05.147446+00:00
-- url     : https://prove2.me/theorems/779fbb25-9696-4c87-b480-0f3d50b33f4e
-- title:
--   A weighted Hölder inequality for cubic means
-- statement:
--   Let $s$ be a finite set and let $a_i,w_i\ge0$ for $i\in s$. Then
--   $$
--   \Bigl(\sum_{i\in s}a_i^2w_i\Bigr)^{3/2}\le\Bigl(\sum_{i\in s}a_i^3w_i\Bigr)\Bigl(\sum_{i\in s}w_i\Bigr)^{1/2} .
--   $$
--
--   The weighted quadratic mean is bounded by the weighted cubic mean. This converts Hilbert–Schmidt bounds into cubic masses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/WeightedCubic.lean#L61-L92

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump

open OAI OAI.TriangularHilbert
universe uι
open scoped BigOperators

theorem OAI.TriangularHilbert.weighted_cubic {ι : Type uι} (s : Finset ι) (a w : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, a i^2*w i) * Real.sqrt (∑ i ∈ s, a i^2*w i) ≤
      (∑ i ∈ s, a i^3*w i) * Real.sqrt (∑ i ∈ s, w i) := by sorry
