-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_pow_prime_pow_mem_not_mem
-- name    : GroundTheory.PAdicHodge.SenTateChar.pow_prime_pow_mem_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:47.54481+00:00
-- url     : https://prove2.me/theorems/aa5ee547-851b-4d6f-b231-f34602c5f22e
-- title:
--   Sen Tate Char: pow prime pow mem not mem
-- statement:
--   The Sen Tate Char construction uses the pow prime pow mem not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L167-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L167-L176

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

theorem GroundTheory.PAdicHodge.SenTateChar.pow_prime_pow_mem_not_mem {s : ℕ} (hs : 2 ≤ s) {a : ℤ_[p]ˣ} (ha : a ∈ unitsOneAdd p s)
    (ha' : a ∉ unitsOneAdd p (s + 1)) (i : ℕ) :
    a ^ p ^ i ∈ unitsOneAdd p (s + i) ∧ a ^ p ^ i ∉ unitsOneAdd p (s + i + 1) := by sorry
