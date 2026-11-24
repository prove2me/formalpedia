-- Prove2me | Theorems.Thm_GlobalTheory_ZetaFractionalIntegral_integrableOn_cpow_neg
-- name    : GlobalTheory.ZetaFractionalIntegral.integrableOn_cpow_neg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:03:56.858056+00:00
-- url     : https://prove2.me/theorems/e78041cd-2b6d-4085-a6ec-6e415fb357ff
-- title:
--   Zeta Fractional Integral: integrable On cpow neg
-- statement:
--   The Zeta Fractional Integral construction uses the integrable On cpow neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ZetaEqSubIntegralFract.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ZetaEqSubIntegralFract.lean#L21-L22

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

theorem GlobalTheory.ZetaFractionalIntegral.integrableOn_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi 1) := by sorry
