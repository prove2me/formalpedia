-- Prove2me | Theorems.Thm_GlobalTheory_GramSchmidtCont_continuousOn_uMat_apply
-- name    : GlobalTheory.GramSchmidtCont.continuousOn_uMat_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:56:40.964119+00:00
-- url     : https://prove2.me/theorems/3adf35b7-88d5-4d6d-a1f4-b97ddb48bcd4
-- title:
--   Gram Schmidt Cont: continuous On u Mat apply
-- statement:
--   The Gram Schmidt Cont construction uses the continuous On u Mat apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsContinuousGramSchmidt.lean#L20-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsContinuousGramSchmidt.lean#L20-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsContinuousGramSchmidt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.GramSchmidtCont
open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

theorem GlobalTheory.GramSchmidtCont.continuousOn_uMat_apply {T : Type} [TopologicalSpace T] {n : ℕ} {s : Set T}
    {M : T → Matrix (Fin n) (Fin n) ℂ} (hM : Continuous M)
    (hd : ∀ t ∈ s, ∀ c : Fin n, (blk (M t) c).det ≠ 0) (j c : Fin n) :
    ContinuousOn (fun t => uMat (M t) j c) s := by sorry
