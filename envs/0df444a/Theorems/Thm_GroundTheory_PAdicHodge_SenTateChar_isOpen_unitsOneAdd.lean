-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_isOpen_unitsOneAdd
-- name    : GroundTheory.PAdicHodge.SenTateChar.isOpen_unitsOneAdd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:38.978395+00:00
-- url     : https://prove2.me/theorems/4ee90206-870d-462a-b042-0b043fd0e8db
-- title:
--   Sen Tate Char: is Open units One Add
-- statement:
--   The Sen Tate Char construction uses the is Open units One Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L52-L60

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.SenTateChar
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}

theorem GroundTheory.PAdicHodge.SenTateChar.isOpen_unitsOneAdd (k : ℕ) : IsOpen (unitsOneAdd p k : Set ℤ_[p]ˣ) := by sorry
