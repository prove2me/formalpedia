-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_dvd_one_add_pow_sub
-- name    : GroundTheory.PAdicHodge.SenTateChar.dvd_one_add_pow_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:48.624552+00:00
-- url     : https://prove2.me/theorems/c6e91aca-0306-420f-b91a-5cb8a99130db
-- title:
--   Sen Tate Char: dvd one add pow sub
-- statement:
--   The Sen Tate Char construction uses the dvd one add pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L62-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L62-L98

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

theorem GroundTheory.PAdicHodge.SenTateChar.dvd_one_add_pow_sub {k : ℕ} (hk : 2 ≤ k) {x : ℤ_[p]} (hx : (p : ℤ_[p]) ^ k ∣ x) :
    (p : ℤ_[p]) ^ (k + 2) ∣ (1 + x) ^ p - 1 - p * x := by sorry
