-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_exists_level
-- name    : GroundTheory.PAdicHodge.SenTateChar.exists_level
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:22.380797+00:00
-- url     : https://prove2.me/theorems/5a1f19f3-eb5b-4e11-b7bc-13ed3597091a
-- title:
--   Sen Tate Char: exists level
-- statement:
--   The Sen Tate Char construction uses the exists level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L191-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L191-L214

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

theorem GroundTheory.PAdicHodge.SenTateChar.exists_level {a : ℤ_[p]ˣ} (ha : a ≠ 1) :
    ∃ s, a ∈ unitsOneAdd p s ∧ a ∉ unitsOneAdd p (s + 1) := by sorry
