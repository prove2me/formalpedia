-- Prove2me | Theorems.Thm_GroundTheory_Global_integrable_norm_pow_smul_complexGaussian
-- name    : GroundTheory.Global.integrable_norm_pow_smul_complexGaussian
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:54.750079+00:00
-- url     : https://prove2.me/theorems/8f838eba-2033-46a3-ab3a-6b6b89a7046a
-- title:
--   Global: integrable norm pow smul complex Gaussian
-- statement:
--   The Global construction uses the integrable norm pow smul complex Gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L79-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L79-L91

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

theorem GroundTheory.Global.integrable_norm_pow_smul_complexGaussian (m : ℤ) (k : ℕ) :
    Integrable (fun z : ℂ ↦ (‖z‖ ^ k : ℝ) • complexGaussian m z) := by sorry
