-- Prove2me | Theorems.Thm_GlobalTheory_QuadFibre_IsSqrtOn_norm_sqrt
-- name    : GlobalTheory.QuadFibre.IsSqrtOn.norm_sqrt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:08:25.546584+00:00
-- url     : https://prove2.me/theorems/6b3cb647-4646-41f8-b629-b1ec9364e484
-- title:
--   Is Sqrt On: norm sqrt
-- statement:
--   The Is Sqrt On construction uses the norm sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegrableContinuousOnAveragedFibreIntegral.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IntegrableContinuousOnAveragedFibreIntegral.lean#L47-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegrableContinuousOnAveragedFibreIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.QuadFibre

theorem GlobalTheory.QuadFibre.IsSqrtOn.norm_sqrt {K : Type} [NormedField K] {U : Set K} {s : K → K}
    (h : IsSqrtOn U s) {a : K} (ha : a ∈ U) : ‖s a‖ = 1 := by sorry
