-- Prove2me | Theorems.Thm_OAI_TriangularHilbert_sum_windowMask_variation
-- name    : OAI.TriangularHilbert.sum_windowMask_variation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T02:20:50.268692+00:00
-- url     : https://prove2.me/theorems/f5f8926a-c3d7-456b-9230-72790fc5b80c
-- title:
--   Total variation of a window switch along increasing times
-- statement:
--   For thresholds $a\le b$, a complex number $A$ and the window switch $\mathrm{windowMask}(a,b,s,A)=A\,\mathbf 1_{a\le s<b}$, let $t_0\le t_1\le\dots$ be nondecreasing times. Then for every $n$,
--   $$
--   \sum_{k<n}\bigl|\mathrm{windowMask}(a,b,t_{k+1},A)-\mathrm{windowMask}(a,b,t_k,A)\bigr|\le2|A| .
--   $$
--
--   An entry that is switched on once and off once has total variation at most $2|A|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/Switch.lean#L49-L62

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch

open OAI OAI.TriangularHilbert
open scoped BigOperators

theorem OAI.TriangularHilbert.sum_windowMask_variation (t : ℕ → ℝ) (ht : Monotone t) (a b : ℝ) (hab : a ≤ b)
    (A : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ‖windowMask a b (t (k+1)) A-windowMask a b (t k) A‖) ≤ 2*‖A‖ := by sorry
