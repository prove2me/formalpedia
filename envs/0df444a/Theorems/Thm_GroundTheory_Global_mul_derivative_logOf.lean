-- Prove2me | Theorems.Thm_GroundTheory_Global_mul_derivative_logOf
-- name    : GroundTheory.Global.mul_derivative_logOf
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:12.399349+00:00
-- url     : https://prove2.me/theorems/bb85f6d8-fff2-45b6-81e6-9198149d4e31
-- title:
--   Global: mul derivative log Of
-- statement:
--   The Global construction uses the mul derivative log Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L96-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L96-L113

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GroundTheory GroundTheory.Global
variable {k : Type*} [Field k] [CharZero k]

theorem GroundTheory.Global.mul_derivative_logOf (f : PowerSeries k) (hf : PowerSeries.constantCoeff f = 1) :
    f * PowerSeries.derivative k (PowerSeries.logOf f) = PowerSeries.derivative k f := by sorry
