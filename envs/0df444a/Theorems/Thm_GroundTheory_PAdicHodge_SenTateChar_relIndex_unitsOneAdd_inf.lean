-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_relIndex_unitsOneAdd_inf
-- name    : GroundTheory.PAdicHodge.SenTateChar.relIndex_unitsOneAdd_inf
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:16.461994+00:00
-- url     : https://prove2.me/theorems/e147aa81-f012-4e9f-a25b-1ff2dce05e0b
-- title:
--   Sen Tate Char: rel Index units One Add inf
-- statement:
--   The Sen Tate Char construction uses the rel Index units One Add inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L281-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L281-L293

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

theorem GroundTheory.PAdicHodge.SenTateChar.relIndex_unitsOneAdd_inf {s : ℕ} (hs : 2 ≤ s) (R : Subgroup ℤ_[p]ˣ) {a : ℤ_[p]ˣ}
    (haR : a ∈ R) (ha : a ∈ unitsOneAdd p s) (ha' : a ∉ unitsOneAdd p (s + 1)) (i : ℕ) :
    (unitsOneAdd p (s + i) ⊓ R).relIndex (unitsOneAdd p s ⊓ R) = p ^ i := by sorry
