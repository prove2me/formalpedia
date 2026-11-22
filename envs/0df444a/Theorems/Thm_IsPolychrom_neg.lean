-- Prove2me | Theorems.Thm_IsPolychrom_neg
-- name    : IsPolychrom.neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:34:56.397633+00:00
-- url     : https://prove2.me/theorems/e97043b5-3338-45b5-aae7-97752d9a8a6e
-- title:
--   Is Polychrom: neg
-- statement:
--   The Is Polychrom construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L122-L127
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L122-L127

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

theorem IsPolychrom.neg [DecidableEq G] (h : IsPolychrom S χ) :
    IsPolychrom (-S) (fun g ↦ χ (-g)) := by sorry
