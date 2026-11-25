-- Prove2me | Theorems.Thm_GroundTheory_Global_complexFourier_mul_self
-- name    : GroundTheory.Global.complexFourier_mul_self
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:25.161438+00:00
-- url     : https://prove2.me/theorems/100a98ba-4623-4fd3-9ea0-b244ea3db178
-- title:
--   Global: complex Fourier mul self
-- statement:
--   The Global construction uses the complex Fourier mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplexFourier.lean#L11-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplexFourier.lean#L11-L45

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

theorem GroundTheory.Global.complexFourier_mul_self {f : ℂ → ℂ} (hf : Integrable f complexPlaceMeasure)
    (hf' : Integrable (fun z ↦ ‖z‖ * ‖f z‖) complexPlaceMeasure) {w : ℂ} {D : ℂ →L[ℝ] ℂ}
    (hD : HasFDerivAt (complexFourier f) D w) :
    -4 * π * I * complexFourier (fun z ↦ z * f z) w = D 1 - I * D I := by sorry
