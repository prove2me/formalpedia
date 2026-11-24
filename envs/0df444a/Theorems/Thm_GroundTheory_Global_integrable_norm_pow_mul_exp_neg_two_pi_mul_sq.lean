-- Prove2me | Theorems.Thm_GroundTheory_Global_integrable_norm_pow_mul_exp_neg_two_pi_mul_sq
-- name    : GroundTheory.Global.integrable_norm_pow_mul_exp_neg_two_pi_mul_sq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:15.783834+00:00
-- url     : https://prove2.me/theorems/1577edd2-1b15-4eb0-9818-db260a429640
-- title:
--   Global: integrable norm pow mul exp neg two pi mul sq
-- statement:
--   The Global construction uses the integrable norm pow mul exp neg two pi mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L67-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L67-L77

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
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
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform ENNReal
noncomputable section

theorem GroundTheory.Global.integrable_norm_pow_mul_exp_neg_two_pi_mul_sq (k : ℕ) :
    Integrable (fun z : ℂ ↦ ‖z‖ ^ k * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by sorry
