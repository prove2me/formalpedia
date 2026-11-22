-- Prove2me | Theorems.Thm_HasPolychromColouring_of_surjective
-- name    : HasPolychromColouring.of_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:35:19.675332+00:00
-- url     : https://prove2.me/theorems/75197e8a-0003-4d47-8473-2a184687dcf3
-- title:
--   Has Polychrom Colouring: of surjective
-- statement:
--   If `S` has a `K₁`-polychromatic colouring and `f : K₁ → K₂` is surjective,
--   then `S` has a `K₂`-polychromatic colouring.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L176-L180
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L176-L180

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset

theorem HasPolychromColouring.of_surjective {K₁ K₂ : Type*}
    (h₁ : HasPolychromColouring K₁ S) {f : K₁ → K₂} (hf : f.Surjective) :
    HasPolychromColouring K₂ S := by sorry
