-- Prove2me | Theorems.Thm_GlobalTheory_integrable_norm_pow_mul_exp_neg_mul_norm_sq
-- name    : GlobalTheory.integrable_norm_pow_mul_exp_neg_mul_norm_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:04.976806+00:00
-- url     : https://prove2.me/theorems/95782af1-9c70-5ebd-adc5-50b2d89a98f1
-- title:
--   Global Theory: integrable norm pow mul exp neg mul norm sq
-- statement:
--   The Global Theory construction uses the integrable norm pow mul exp neg mul norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableMonomialMulConjComplexGaussian.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableMonomialMulConjComplexGaussian.lean#L42-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped Nat ComplexConjugate
open GlobalTheory
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {E}

theorem GlobalTheory.integrable_norm_pow_mul_exp_neg_mul_norm_sq (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable fun z : E => ‖z‖ ^ n * exp (-b * ‖z‖ ^ 2) := by sorry
