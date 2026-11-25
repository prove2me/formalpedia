-- Prove2me | Theorems.Thm_GroundTheory_Global_hasDerivAt_realGaussian
-- name    : GroundTheory.Global.hasDerivAt_realGaussian
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:41:09.554556+00:00
-- url     : https://prove2.me/theorems/033d5e25-a5f7-41ee-92c4-ed627b8f7055
-- title:
--   Global: has Deriv At real Gaussian
-- statement:
--   The Global construction uses the has Deriv At real Gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Gaussian.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Gaussian.lean#L42-L49

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
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
open Complex MeasureTheory Set Real
open scoped FourierTransform
noncomputable section

theorem GroundTheory.Global.hasDerivAt_realGaussian (x : ℝ) :
    HasDerivAt realGaussian (-2 * π * x * realGaussian x) x := by sorry
