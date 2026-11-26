-- Prove2me | Theorems.Thm_Malliavin_exists_strictMono_comp_of_injective
-- name    : Malliavin.exists_strictMono_comp_of_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:06.610877+00:00
-- url     : https://prove2.me/theorems/526329d8-cf0f-53d3-beb6-8f47a8f0b0ef
-- title:
--   Malliavin: exists strict Mono comp of injective
-- statement:
--   Every injective tuple is sorted by some permutation (namely `Tuple.sort`).
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L110-L113
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L110-L113

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]

theorem Malliavin.exists_strictMono_comp_of_injective {n : ℕ} {t : Fin n → T}
    (ht : Function.Injective t) : ∃ σ : Equiv.Perm (Fin n), StrictMono (t ∘ σ) := by sorry
