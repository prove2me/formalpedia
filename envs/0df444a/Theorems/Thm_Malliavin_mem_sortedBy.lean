-- Prove2me | Theorems.Thm_Malliavin_mem_sortedBy
-- name    : Malliavin.mem_sortedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:57.157707+00:00
-- url     : https://prove2.me/theorems/8deed797-a771-4c58-9370-93f67580c846
-- title:
--   Malliavin: mem sorted By
-- statement:
--   The Malliavin construction uses the mem sorted By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L93-L95
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L93-L95

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]

theorem Malliavin.mem_sortedBy {n : ℕ} {σ : Equiv.Perm (Fin n)} {t : Fin n → T} :
    t ∈ sortedBy T n σ ↔ StrictMono (t ∘ σ) := by sorry
