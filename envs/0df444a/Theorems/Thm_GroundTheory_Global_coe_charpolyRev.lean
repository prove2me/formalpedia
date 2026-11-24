-- Prove2me | Theorems.Thm_GroundTheory_Global_coe_charpolyRev
-- name    : GroundTheory.Global.coe_charpolyRev
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:39:59.066032+00:00
-- url     : https://prove2.me/theorems/d33919e3-e47f-401f-ab20-7804b8dd0f84
-- title:
--   Global: coe charpoly Rev
-- statement:
--   The Global construction uses the coe charpoly Rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L42-L49

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
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem GroundTheory.Global.coe_charpolyRev (M : Matrix n n R) :
    ((M.charpolyRev : R[X]) : PowerSeries R) =
      (1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C).det := by sorry
