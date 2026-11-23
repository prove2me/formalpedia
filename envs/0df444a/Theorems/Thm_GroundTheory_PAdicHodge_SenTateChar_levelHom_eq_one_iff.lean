-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_levelHom_eq_one_iff
-- name    : GroundTheory.PAdicHodge.SenTateChar.levelHom_eq_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:54.534544+00:00
-- url     : https://prove2.me/theorems/f734de64-a516-493a-8b29-47b6209761ea
-- title:
--   Sen Tate Char: level Hom eq one iff
-- statement:
--   The Sen Tate Char construction uses the level Hom eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L159-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L159-L165

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

theorem GroundTheory.PAdicHodge.SenTateChar.levelHom_eq_one_iff {k : ℕ} (hk : 1 ≤ k) (u : unitsOneAdd p k) :
    levelHom p k hk u = 1 ↔ (u : ℤ_[p]ˣ) ∈ unitsOneAdd p (k + 1) := by sorry
