-- Prove2me | Theorems.Thm_Malliavin_measurable_comp_perm
-- name    : Malliavin.measurable_comp_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:48:07.611409+00:00
-- url     : https://prove2.me/theorems/9e66fca5-4155-48a9-858f-4368826000ca
-- title:
--   Malliavin: measurable comp perm
-- statement:
--   The Malliavin construction uses the measurable comp perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L149-L151
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L149-L151

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T]

theorem Malliavin.measurable_comp_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Measurable fun t : Fin n → T => t ∘ σ := by sorry
