-- Prove2me | Theorems.Thm_HasPolychromColouring_subset
-- name    : HasPolychromColouring.subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:35:03.816113+00:00
-- url     : https://prove2.me/theorems/a78a287b-5fb2-4e66-9058-5c6605a583c3
-- title:
--   Has Polychrom Colouring: subset
-- statement:
--   If `S'` has a `K`-polychromatic colouring and `S' ⊆ S`, then `S` also has one.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L169-L172
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L169-L172

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

theorem HasPolychromColouring.subset {S' : Finset G} (h : HasPolychromColouring K S') (hS : S' ⊆ S) :
    HasPolychromColouring K S := by sorry
