-- Prove2me | Theorems.Thm_GroundTheory_Global_complexFourier_eq_fourierIntegral
-- name    : GroundTheory.Global.complexFourier_eq_fourierIntegral
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:17.299446+00:00
-- url     : https://prove2.me/theorems/d1a739e1-4a87-4fcb-97ee-3ec74204d94f
-- title:
--   Global: complex Fourier eq fourier Integral
-- statement:
--   The Global construction uses the complex Fourier eq fourier Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L22-L26

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

theorem GroundTheory.Global.complexFourier_eq_fourierIntegral (f : ℂ → ℂ) :
    complexFourier f =
      VectorFourier.fourierIntegral 𝐞 complexPlaceMeasure traceFormℂ.toLinearMap₁₂ f := by sorry
