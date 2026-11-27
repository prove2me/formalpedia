-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_pow_not_mem_of_not_dvd
-- name    : GroundTheory.PAdicHodge.SenTateChar.pow_not_mem_of_not_dvd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:09.984712+00:00
-- url     : https://prove2.me/theorems/45207018-d24e-458d-9175-b641c2a07dfa
-- title:
--   Sen Tate Char: pow not mem of not dvd
-- statement:
--   The Sen Tate Char construction uses the pow not mem of not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L178-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L178-L189

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

theorem GroundTheory.PAdicHodge.SenTateChar.pow_not_mem_of_not_dvd {s : ℕ} (hs : 1 ≤ s) {a : ℤ_[p]ˣ} (ha : a ∈ unitsOneAdd p s)
    (ha' : a ∉ unitsOneAdd p (s + 1)) {m : ℕ} (hm : ¬ p ∣ m) :
    a ^ m ∈ unitsOneAdd p s ∧ a ^ m ∉ unitsOneAdd p (s + 1) := by sorry
