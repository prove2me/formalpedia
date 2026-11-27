-- Prove2me | Theorems.Thm_GroundTheory_Global_complexFourier_complexGaussian
-- name    : GroundTheory.Global.complexFourier_complexGaussian
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:11.571823+00:00
-- url     : https://prove2.me/theorems/742bc801-1f67-4a9b-a8b4-8e77227fa797
-- title:
--   Global: complex Fourier complex Gaussian
-- statement:
--   The Global construction uses the complex Fourier complex Gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplexFourier.lean#L158-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplexFourier.lean#L158-L165

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

theorem GroundTheory.Global.complexFourier_complexGaussian (m : ℤ) :
    complexFourier (complexGaussian m) = fun w ↦ (-I) ^ m.natAbs * complexGaussian (-m) w := by sorry
