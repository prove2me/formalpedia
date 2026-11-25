-- Prove2me | Theorems.Thm_GroundTheory_Global_integrable_realGaussianOdd
-- name    : GroundTheory.Global.integrable_realGaussianOdd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:02.218774+00:00
-- url     : https://prove2.me/theorems/98c375a8-38d0-4b3e-ac42-82396c7330f4
-- title:
--   Global: integrable real Gaussian Odd
-- statement:
--   The Global construction uses the integrable real Gaussian Odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Gaussian.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/Gaussian.lean#L39-L40

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

theorem GroundTheory.Global.integrable_realGaussianOdd : Integrable realGaussianOdd := by sorry
