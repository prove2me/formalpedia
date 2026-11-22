-- Prove2me | Theorems.Thm_IsPolychrom_card_le
-- name    : IsPolychrom.card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:35:07.035784+00:00
-- url     : https://prove2.me/theorems/5100dc15-0c87-4d1a-9185-2d4536462353
-- title:
--   Is Polychrom: card le
-- statement:
--   The Is Polychrom construction uses the card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L104-L106
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L104-L106

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

theorem IsPolychrom.card_le [Fintype K] (hχ : IsPolychrom S χ) :
    Fintype.card K ≤ #S := by sorry
