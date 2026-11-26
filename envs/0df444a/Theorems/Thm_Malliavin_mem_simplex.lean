-- Prove2me | Theorems.Thm_Malliavin_mem_simplex
-- name    : Malliavin.mem_simplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:06.885654+00:00
-- url     : https://prove2.me/theorems/2852cb23-f46d-4c50-80a0-796d7bf9d955
-- title:
--   Malliavin: mem simplex
-- statement:
--   The Malliavin construction uses the mem simplex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L86-L87
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L86-L87

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]

theorem Malliavin.mem_simplex {n : ℕ} {t : Fin n → T} : t ∈ simplex T n ↔ StrictMono t := by sorry
