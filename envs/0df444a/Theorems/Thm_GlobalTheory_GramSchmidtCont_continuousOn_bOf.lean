-- Prove2me | Theorems.Thm_GlobalTheory_GramSchmidtCont_continuousOn_bOf
-- name    : GlobalTheory.GramSchmidtCont.continuousOn_bOf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:56:32.466395+00:00
-- url     : https://prove2.me/theorems/89285ba8-2663-4721-8725-57d7a9b80870
-- title:
--   Gram Schmidt Cont: continuous On b Of
-- statement:
--   The Gram Schmidt Cont construction uses the continuous On b Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsContinuousGramSchmidt.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsContinuousGramSchmidt.lean#L77-L81

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

theorem GlobalTheory.GramSchmidtCont.continuousOn_bOf {r : ℕ} (X : Data E r) : ContinuousOn (bOf X) X.dom := by sorry
