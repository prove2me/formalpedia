-- Prove2me | Theorems.Thm_GroundTheory_Global_reverse_charpoly_eq_charpolyRev
-- name    : GroundTheory.Global.reverse_charpoly_eq_charpolyRev
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:00.307006+00:00
-- url     : https://prove2.me/theorems/018a8d54-841f-4934-81fe-1583b10eeb94
-- title:
--   Global: reverse charpoly eq charpoly Rev
-- statement:
--   The Global construction uses the reverse charpoly eq charpoly Rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L122-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L122-L125

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

theorem GroundTheory.Global.reverse_charpoly_eq_charpolyRev {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k W) (A : Module.End k W) :
    A.charpoly.reverse = (LinearMap.toMatrix b b A).charpolyRev := by sorry
