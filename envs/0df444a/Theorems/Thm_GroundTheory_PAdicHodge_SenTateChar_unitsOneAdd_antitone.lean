-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_unitsOneAdd_antitone
-- name    : GroundTheory.PAdicHodge.SenTateChar.unitsOneAdd_antitone
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:30.402799+00:00
-- url     : https://prove2.me/theorems/791448da-4059-4858-936b-c53adab69f1d
-- title:
--   Sen Tate Char: units One Add antitone
-- statement:
--   The Sen Tate Char construction uses the units One Add antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L33-L34

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

theorem GroundTheory.PAdicHodge.SenTateChar.unitsOneAdd_antitone : Antitone (unitsOneAdd p) := by sorry
