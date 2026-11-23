-- Prove2me | Theorems.Thm_GroundTheory_Global_complexGaussian_zero
-- name    : GroundTheory.Global.complexGaussian_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:21.356291+00:00
-- url     : https://prove2.me/theorems/076251d8-42bc-4bd2-a462-8300e68fccf7
-- title:
--   Global: complex Gaussian zero
-- statement:
--   The Global construction uses the complex Gaussian zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L31-L33

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

theorem GroundTheory.Global.complexGaussian_zero (z : ℂ) :
    complexGaussian 0 z = Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by sorry
