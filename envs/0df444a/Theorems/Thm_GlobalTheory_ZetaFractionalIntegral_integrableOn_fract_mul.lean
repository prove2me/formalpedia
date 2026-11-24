-- Prove2me | Theorems.Thm_GlobalTheory_ZetaFractionalIntegral_integrableOn_fract_mul
-- name    : GlobalTheory.ZetaFractionalIntegral.integrableOn_fract_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:03:42.112979+00:00
-- url     : https://prove2.me/theorems/7de3ccc7-0dcc-453a-8c2f-361c105c1d6b
-- title:
--   Zeta Fractional Integral: integrable On fract mul
-- statement:
--   The Zeta Fractional Integral construction uses the integrable On fract mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ZetaEqSubIntegralFract.lean#L24-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ZetaEqSubIntegralFract.lean#L24-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ZetaFractionalIntegral
open MeasureTheory Set Filter Asymptotics

theorem GlobalTheory.ZetaFractionalIntegral.integrableOn_fract_mul {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by sorry
