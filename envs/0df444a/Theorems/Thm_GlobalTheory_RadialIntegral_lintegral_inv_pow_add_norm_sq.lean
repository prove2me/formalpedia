-- Prove2me | Theorems.Thm_GlobalTheory_RadialIntegral_lintegral_inv_pow_add_norm_sq
-- name    : GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:38.462628+00:00
-- url     : https://prove2.me/theorems/4a145ec9-80e0-420e-a6ba-5d751e4abbf2
-- title:
--   Radial Integral: lintegral inv pow add norm sq
-- statement:
--   The Radial Integral construction uses the lintegral inv pow add norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralComplexInvPowAddNormSq.lean#L43-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralComplexInvPowAddNormSq.lean#L43-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralComplexInvPowAddNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.RadialIntegral

theorem GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal (Real.pi / ((m + 1) * a ^ (m + 1))) := by sorry
