-- Prove2me | Theorems.Thm_GlobalTheory_GramSchmidtCont_continuousOn_sOf
-- name    : GlobalTheory.GramSchmidtCont.continuousOn_sOf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:57:03.557355+00:00
-- url     : https://prove2.me/theorems/8c3a4b39-6bf4-4ce4-9f3b-13ff6cfdfcac
-- title:
--   Gram Schmidt Cont: continuous On s Of
-- statement:
--   The Gram Schmidt Cont construction uses the continuous On s Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsContinuousGramSchmidt.lean#L68-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsContinuousGramSchmidt.lean#L68-L75

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.GramSchmidtCont.continuousOn_sOf {r : ℕ} (X : Data E r) (τ : X.Ψ) (k : Fin r) :
    ContinuousOn (fun x : Frame X.Ψ r => sOf X x τ k) X.dom := by sorry
