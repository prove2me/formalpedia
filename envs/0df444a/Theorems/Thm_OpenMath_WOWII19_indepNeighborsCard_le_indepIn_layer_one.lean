-- Prove2me | Theorems.Thm_OpenMath_WOWII19_indepNeighborsCard_le_indepIn_layer_one
-- name    : OpenMath.WOWII19.indepNeighborsCard_le_indepIn_layer_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:25.536625+00:00
-- url     : https://prove2.me/theorems/f61ae316-cb7f-4749-a95a-5c068e69f276
-- title:
--   WOWII19: indep Neighbors Card le indep In layer one
-- statement:
--   Layer `1` is the neighbourhood.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L157-L163
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L157-L163

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : SimpleGraph α}

theorem OpenMath.WOWII19.indepNeighborsCard_le_indepIn_layer_one (v : α) :
    indepNeighborsCard G v ≤ indepIn G (layer G v 1) := by sorry
