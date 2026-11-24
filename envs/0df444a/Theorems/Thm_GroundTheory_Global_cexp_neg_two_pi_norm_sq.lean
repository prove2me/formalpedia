-- Prove2me | Theorems.Thm_GroundTheory_Global_cexp_neg_two_pi_norm_sq
-- name    : GroundTheory.Global.cexp_neg_two_pi_norm_sq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:34.879126+00:00
-- url     : https://prove2.me/theorems/c8b2fd0d-361e-47d8-81aa-4f5eb9c94247
-- title:
--   Global: cexp neg two pi norm sq
-- statement:
--   The Global construction uses the cexp neg two pi norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplexFourier.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplexFourier.lean#L47-L52

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
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
open scoped FourierTransform
noncomputable section

theorem GroundTheory.Global.cexp_neg_two_pi_norm_sq (w : ℂ) :
    Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2) = Complex.exp (-2 * π * (w * conj w)) := by sorry
