-- Prove2me | Theorems.Thm_GlobalTheory_UnfoldComplex_continuous_lact
-- name    : GlobalTheory.UnfoldComplex.continuous_lact
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:24.361945+00:00
-- url     : https://prove2.me/theorems/f5beb6f7-9d70-5daa-a952-58884f43e4a9
-- title:
--   Unfold Complex: continuous lact
-- statement:
--   The Unfold Complex construction uses the continuous lact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IntegralEqIntegralTsumOfLintegral.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IntegralEqIntegralTsumOfLintegral.lean#L42-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IntegralEqIntegralTsumOfLintegral
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
open GlobalTheory GlobalTheory.UnfoldComplex
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.UnfoldComplex.continuous_lact {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) :
    Continuous (fun y : Frame Ψ r => lact δ y) := by sorry
