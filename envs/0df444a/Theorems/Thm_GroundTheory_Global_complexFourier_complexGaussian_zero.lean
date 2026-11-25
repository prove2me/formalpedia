-- Prove2me | Theorems.Thm_GroundTheory_Global_complexFourier_complexGaussian_zero
-- name    : GroundTheory.Global.complexFourier_complexGaussian_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:15.12646+00:00
-- url     : https://prove2.me/theorems/2a9d3920-7f12-4903-aa99-189059242a6f
-- title:
--   Global: complex Fourier complex Gaussian zero
-- statement:
--   The Global construction uses the complex Fourier complex Gaussian zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L46-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L46-L65

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

theorem GroundTheory.Global.complexFourier_complexGaussian_zero :
    complexFourier (complexGaussian 0) = complexGaussian 0 := by sorry
