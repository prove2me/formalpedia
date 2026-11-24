-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_pow_prime_mem_iff
-- name    : GroundTheory.PAdicHodge.SenTateChar.pow_prime_mem_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:29.160256+00:00
-- url     : https://prove2.me/theorems/7fdfe476-5bae-446e-83f8-6b56469357f3
-- title:
--   Sen Tate Char: pow prime mem iff
-- statement:
--   The Sen Tate Char construction uses the pow prime mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L100-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L100-L118

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

theorem GroundTheory.PAdicHodge.SenTateChar.pow_prime_mem_iff {k : ℕ} (hk : 2 ≤ k) {u : ℤ_[p]ˣ} (hu : u ∈ unitsOneAdd p k) :
    u ^ p ∈ unitsOneAdd p (k + 1) ∧ (u ^ p ∈ unitsOneAdd p (k + 2) ↔ u ∈ unitsOneAdd p (k + 1)) := by sorry
