-- Prove2me | Theorems.Thm_OpenMath_WOWII96_indepNum_le_one_of_local
-- name    : OpenMath.WOWII96.indepNum_le_one_of_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:37:29.389943+00:00
-- url     : https://prove2.me/theorems/3b58dda7-893c-548e-b66a-0eeb31f64547
-- title:
--   WOWII96: indep Num le one of local
-- statement:
--   If every neighbourhood has independence number at most `1`, the connected graph is
--   complete, hence its independence number is at most `1`.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII96.lean#L51-L79
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII96.lean#L51-L79

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_OpenMath_WOWII96
set_option autoImplicit true
@[expose] public section
public section
open OpenMath OpenMath.WOWII96
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OpenMath.WOWII96.indepNum_le_one_of_local {G : SimpleGraph α} (h : G.Connected)
    (hL : ∀ u, indepNeighborsCard G u ≤ 1) : G.indepNum ≤ 1 := by sorry
