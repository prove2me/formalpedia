-- Prove2me | Theorems.Thm_GlobalTheory_ClosedDiscontinuity_propDisc_and_la1GG
-- name    : GlobalTheory.ClosedDiscontinuity.propDisc_and_la1GG
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:13:36.302298+00:00
-- url     : https://prove2.me/theorems/db82c18f-73cc-48e7-b432-d717ea4a6c0b
-- title:
--   Closed Discontinuity: prop Disc and la1 GG
-- statement:
--   The Closed Discontinuity construction uses the prop Disc and la1 GG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FirstMinimumInvariantContinuousPosOnFrames.lean#L392-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FirstMinimumInvariantContinuousPosOnFrames.lean#L392-L394

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajLactRmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EventuallyComparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RmulOneFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPosOnFrames
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
open GlobalTheory GlobalTheory.ClosedDiscontinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.ClosedDiscontinuity.propDisc_and_la1GG :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X) ∧ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.LineBundleFirstBoundGlobalGeneration (E := E)) := by sorry
