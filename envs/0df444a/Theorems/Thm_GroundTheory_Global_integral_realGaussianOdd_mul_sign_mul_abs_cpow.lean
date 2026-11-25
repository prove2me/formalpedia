-- Prove2me | Theorems.Thm_GroundTheory_Global_integral_realGaussianOdd_mul_sign_mul_abs_cpow
-- name    : GroundTheory.Global.integral_realGaussianOdd_mul_sign_mul_abs_cpow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:08.288535+00:00
-- url     : https://prove2.me/theorems/ccf2ca11-3c8e-4176-88c2-8277017f544d
-- title:
--   Global: integral real Gaussian Odd mul sign mul abs cpow
-- statement:
--   The Global construction uses the integral real Gaussian Odd mul sign mul abs cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Gaussian.lean#L107-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Gaussian.lean#L107-L137

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real
open scoped FourierTransform
noncomputable section

theorem GroundTheory.Global.integral_realGaussianOdd_mul_sign_mul_abs_cpow {s : ℂ} (hs : -1 < s.re) :
    ∫ x : ℝ, realGaussianOdd x * (Real.sign x : ℂ) * ((|x| : ℝ) : ℂ) ^ s / ((|x| : ℝ) : ℂ) =
      Gammaℝ (s + 1) := by sorry
