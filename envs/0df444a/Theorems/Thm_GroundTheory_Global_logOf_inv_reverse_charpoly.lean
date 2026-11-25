-- Prove2me | Theorems.Thm_GroundTheory_Global_logOf_inv_reverse_charpoly
-- name    : GroundTheory.Global.logOf_inv_reverse_charpoly
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:32.877263+00:00
-- url     : https://prove2.me/theorems/8a87aca1-d113-44c5-a8b0-f12d4d17c989
-- title:
--   Global: log Of inv reverse charpoly
-- statement:
--   The Global construction uses the log Of inv reverse charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L143-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L143-L169

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
variable {k W W' : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']

theorem GroundTheory.Global.logOf_inv_reverse_charpoly [CharZero k] (A : Module.End k W) :
    PowerSeries.logOf ((A.charpoly.reverse : PowerSeries k)⁻¹) =
      PowerSeries.mk fun m => if m = 0 then 0 else LinearMap.trace k W (A ^ m) / m := by sorry
