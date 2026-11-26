-- Prove2me | Theorems.Thm_Malliavin_mem_symmetricSubmodule
-- name    : Malliavin.mem_symmetricSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:42:18.169219+00:00
-- url     : https://prove2.me/theorems/4df7c9f3-8391-4341-9658-b1b74edaddd4
-- title:
--   Malliavin: mem symmetric Submodule
-- statement:
--   The Malliavin construction uses the mem symmetric Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L168-L170
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L168-L170

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [AddCommGroup E] [Module ℝ E]

theorem Malliavin.mem_symmetricSubmodule {n : ℕ} {f : (Fin n → T) → E} :
    f ∈ symmetricSubmodule T E n ↔ IsSymmetric n f := by sorry
