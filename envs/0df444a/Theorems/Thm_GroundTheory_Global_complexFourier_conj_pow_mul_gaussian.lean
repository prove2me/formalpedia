-- Prove2me | Theorems.Thm_GroundTheory_Global_complexFourier_conj_pow_mul_gaussian
-- name    : GroundTheory.Global.complexFourier_conj_pow_mul_gaussian
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:06.696602+00:00
-- url     : https://prove2.me/theorems/9fa51c7c-2578-46df-8f2d-8e97ded8fd05
-- title:
--   Global: complex Fourier conj pow mul gaussian
-- statement:
--   The Global construction uses the complex Fourier conj pow mul gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplexFourier.lean#L145-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplexFourier.lean#L145-L156

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

theorem GroundTheory.Global.complexFourier_conj_pow_mul_gaussian (n : ℕ) :
    complexFourier (fun z ↦ conj z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun w ↦ (-I) ^ n * (w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by sorry
