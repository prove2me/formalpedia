-- Prove2me | Theorems.Thm_Malliavin_mem_diagonal
-- name    : Malliavin.mem_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:49.609014+00:00
-- url     : https://prove2.me/theorems/ae4874f0-069d-41e6-91a5-0fb97b340a7e
-- title:
--   Malliavin: mem diagonal
-- statement:
--   The Malliavin construction uses the mem diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L58-L59
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L58-L59

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}

theorem Malliavin.mem_diagonal {n : ℕ} {t : Fin n → T} : t ∈ diagonal T n ↔ ¬ Function.Injective t := by sorry
