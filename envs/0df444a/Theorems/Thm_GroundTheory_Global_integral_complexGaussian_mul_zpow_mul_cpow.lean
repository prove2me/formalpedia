-- Prove2me | Theorems.Thm_GroundTheory_Global_integral_complexGaussian_mul_zpow_mul_cpow
-- name    : GroundTheory.Global.integral_complexGaussian_mul_zpow_mul_cpow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:09.677472+00:00
-- url     : https://prove2.me/theorems/9b5dcbb2-e74e-422f-a87f-d8bc7e685cc9
-- title:
--   Global: integral complex Gaussian mul zpow mul cpow
-- statement:
--   The Global construction uses the integral complex Gaussian mul zpow mul cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L132-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L132-L169

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

theorem GroundTheory.Global.integral_complexGaussian_mul_zpow_mul_cpow (m : ℤ) {s : ℂ}
    (hs : 0 < s.re + m.natAbs / 2) :
    ∫ z, complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s /
        ((‖z‖ ^ 2 : ℝ) : ℂ) ∂complexPlaceMeasure =
      π * Gammaℂ (s + m.natAbs / 2) := by sorry
