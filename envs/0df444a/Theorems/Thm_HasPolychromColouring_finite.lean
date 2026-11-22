-- Prove2me | Theorems.Thm_HasPolychromColouring_finite
-- name    : HasPolychromColouring.finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:38:31.3073+00:00
-- url     : https://prove2.me/theorems/dee71504-c3bd-4e22-9192-c5e2b89ff072
-- title:
--   Has Polychrom Colouring: finite
-- statement:
--   The Has Polychrom Colouring construction uses the finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L163-L166
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L163-L166

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

theorem HasPolychromColouring.finite (h : HasPolychromColouring K S) :
    Finite K := by sorry
