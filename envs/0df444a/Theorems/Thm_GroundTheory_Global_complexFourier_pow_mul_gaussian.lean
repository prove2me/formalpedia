-- Prove2me | Theorems.Thm_GroundTheory_Global_complexFourier_pow_mul_gaussian
-- name    : GroundTheory.Global.complexFourier_pow_mul_gaussian
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:22.054436+00:00
-- url     : https://prove2.me/theorems/4b424198-dbd1-46e2-b222-6c5632dbef0b
-- title:
--   Global: complex Fourier pow mul gaussian
-- statement:
--   The Global construction uses the complex Fourier pow mul gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplexFourier.lean#L89-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplexFourier.lean#L89-L126

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

theorem GroundTheory.Global.complexFourier_pow_mul_gaussian (n : ℕ) :
    complexFourier (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun w ↦ (-I) ^ n * (conj w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by sorry
