-- Prove2me | Theorems.Thm_GlobalTheory_ProperDiscontinuity_lact_one
-- name    : GlobalTheory.ProperDiscontinuity.lact_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:57:11.575484+00:00
-- url     : https://prove2.me/theorems/8c0fd5b1-036d-46a6-9596-bddd9d978137
-- title:
--   Proper Discontinuity: lact one
-- statement:
--   The Proper Discontinuity construction uses the lact one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RmulOneFrame.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RmulOneFrame.lean#L33-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RmulOneFrame
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
open GlobalTheory GlobalTheory.ProperDiscontinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.ProperDiscontinuity.lact_one {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) :
    lact (1 : GL (Fin r) E) x = x := by sorry
