-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_levelHom_apply
-- name    : GroundTheory.PAdicHodge.SenTateChar.levelHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:38.790794+00:00
-- url     : https://prove2.me/theorems/4ce6e6e4-fdaa-4396-a0d0-1705f5875f21
-- title:
--   Sen Tate Char: level Hom apply
-- statement:
--   The Sen Tate Char construction uses the level Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L156-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SenTateCharUnits.lean#L156-L157

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

theorem GroundTheory.PAdicHodge.SenTateChar.levelHom_apply {k : ℕ} (hk : 1 ≤ k) (u : unitsOneAdd p k) :
    levelHom p k hk u = Multiplicative.ofAdd (PadicInt.toZMod (levelQuot u)) := by sorry
