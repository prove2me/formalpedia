-- Prove2me | Theorems.Thm_GroundTheory_Global_complexFourier_eq_two_mul_fourier
-- name    : GroundTheory.Global.complexFourier_eq_two_mul_fourier
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:03.996406+00:00
-- url     : https://prove2.me/theorems/82969c52-3d31-4894-bfe3-619eb49e73d9
-- title:
--   Global: complex Fourier eq two mul fourier
-- statement:
--   The Global construction uses the complex Fourier eq two mul fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L35-L44

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

theorem GroundTheory.Global.complexFourier_eq_two_mul_fourier (f : ℂ → ℂ) (w : ℂ) :
    complexFourier f w = 2 * 𝓕 f (2 * conj w) := by sorry
