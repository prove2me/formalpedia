-- Prove2me | Theorems.Thm_HasPolychromColouring_card_le
-- name    : HasPolychromColouring.card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:36:36.832552+00:00
-- url     : https://prove2.me/theorems/71a9c6c8-9679-40f2-9e64-4d56b73f785d
-- title:
--   Has Polychrom Colouring: card le
-- statement:
--   The Has Polychrom Colouring construction uses the card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L158-L161
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L158-L161

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

theorem HasPolychromColouring.card_le [Fintype K] (h : HasPolychromColouring K S) :
    Fintype.card K ≤ #S := by sorry
