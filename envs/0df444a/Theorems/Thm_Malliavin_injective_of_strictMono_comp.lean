-- Prove2me | Theorems.Thm_Malliavin_injective_of_strictMono_comp
-- name    : Malliavin.injective_of_strictMono_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:10.866449+00:00
-- url     : https://prove2.me/theorems/2887a755-3085-4310-aee6-fddc62216fc4
-- title:
--   Malliavin: injective of strict Mono comp
-- statement:
--   The Malliavin construction uses the injective of strict Mono comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L101-L107
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Simplex.lean#L101-L107

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [LinearOrder T]

theorem Malliavin.injective_of_strictMono_comp {n : ℕ} {t : Fin n → T} {σ : Equiv.Perm (Fin n)}
    (h : StrictMono (t ∘ σ)) : Function.Injective t := by sorry
