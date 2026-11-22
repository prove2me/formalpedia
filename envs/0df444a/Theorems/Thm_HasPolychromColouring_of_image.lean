-- Prove2me | Theorems.Thm_HasPolychromColouring_of_image
-- name    : HasPolychromColouring.of_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:34:59.810905+00:00
-- url     : https://prove2.me/theorems/dca0e285-7218-40f0-b76f-78a6c91fbbb6
-- title:
--   Has Polychrom Colouring: of image
-- statement:
--   The Has Polychrom Colouring construction uses the of image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L207-L216
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L207-L216

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

theorem HasPolychromColouring.of_image {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [FunLike F G H] [AddHomClass F G H] (φ : F)
    (h : HasPolychromColouring K (S.image φ)) :
    HasPolychromColouring K S := by sorry
