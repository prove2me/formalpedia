-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_mem_unitsOneAdd_iff_norm
-- name    : GroundTheory.PAdicHodge.SenTateChar.mem_unitsOneAdd_iff_norm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:45:48.211939+00:00
-- url     : https://prove2.me/theorems/319f3460-1454-4c3d-95c5-c3ea7acb9242
-- title:
--   Sen Tate Char: mem units One Add iff norm
-- statement:
--   The Sen Tate Char construction uses the mem units One Add iff norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L48-L50

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

theorem GroundTheory.PAdicHodge.SenTateChar.mem_unitsOneAdd_iff_norm {k : ℕ} {u : ℤ_[p]ˣ} :
    u ∈ unitsOneAdd p k ↔ ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by sorry
