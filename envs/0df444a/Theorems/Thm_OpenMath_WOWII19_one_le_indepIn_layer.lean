-- Prove2me | Theorems.Thm_OpenMath_WOWII19_one_le_indepIn_layer
-- name    : OpenMath.WOWII19.one_le_indepIn_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:19.978793+00:00
-- url     : https://prove2.me/theorems/4bacd378-8b9e-4e00-a7a2-079f30710e93
-- title:
--   WOWII19: one le indep In layer
-- statement:
--   Every layer up to the eccentricity is non-empty.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L147-L154
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L147-L154

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

theorem OpenMath.WOWII19.one_le_indepIn_layer (h : G.Connected) (v : α) {i : ℕ} (hi : i ≤ ecc G v) :
    1 ≤ indepIn G (layer G v i) := by sorry
