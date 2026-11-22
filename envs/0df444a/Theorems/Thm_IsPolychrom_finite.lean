-- Prove2me | Theorems.Thm_IsPolychrom_finite
-- name    : IsPolychrom.finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:36:18.504366+00:00
-- url     : https://prove2.me/theorems/3401a9cb-d436-4681-8903-4b5a779cd290
-- title:
--   Is Polychrom: finite
-- statement:
--   The Is Polychrom construction uses the finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L99-L100
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L99-L100

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

theorem IsPolychrom.finite (hχ : IsPolychrom S χ) :
    Finite K := by sorry
