-- Prove2me | Theorems.Thm_GroundTheory_Global_integrable_complexGaussian
-- name    : GroundTheory.Global.integrable_complexGaussian
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:29.271102+00:00
-- url     : https://prove2.me/theorems/232b7000-d943-471f-9ff2-2901c897256f
-- title:
--   Global: integrable complex Gaussian
-- statement:
--   The Global construction uses the integrable complex Gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/GaussianComplex.lean#L97-L99

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

theorem GroundTheory.Global.integrable_complexGaussian (m : ℤ) :
    Integrable (complexGaussian m) complexPlaceMeasure := by sorry
