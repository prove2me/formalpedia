-- Prove2me | Theorems.Thm_Malliavin_perm_eq_of_strictMono_comp
-- name    : Malliavin.perm_eq_of_strictMono_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:17.855678+00:00
-- url     : https://prove2.me/theorems/78af4860-fc17-4052-9492-e1da314e908e
-- title:
--   Malliavin: perm eq of strict Mono comp
-- statement:
--   The sorting permutation of an injective tuple is unique.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L116-L121
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L116-L121

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]

theorem Malliavin.perm_eq_of_strictMono_comp {n : ℕ} {t : Fin n → T} (ht : Function.Injective t)
    {σ τ : Equiv.Perm (Fin n)} (hσ : StrictMono (t ∘ σ)) (hτ : StrictMono (t ∘ τ)) : σ = τ := by sorry
