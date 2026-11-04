-- Prove2me | Theorems.Thm_Light_Ends_append
-- name    : Light.Ends.append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:36.428202+00:00
-- url     : https://prove2.me/theorems/c04bdecd-2901-4b49-a771-b30f112fa8c6
-- title:
--   Ends: append
-- statement:
--   What is proved about a program holds for the program with more procedures appended.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L89-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L89-L92

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
public import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem Light.Ends.append {s σ T Q} (h : Ends lim P d s σ T Q) (R : Program) :
    Ends lim (P ++ R) d s σ T Q := by sorry
