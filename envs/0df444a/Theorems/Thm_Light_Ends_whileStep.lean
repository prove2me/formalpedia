-- Prove2me | Theorems.Thm_Light_Ends_whileStep
-- name    : Light.Ends.whileStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:42.362261+00:00
-- url     : https://prove2.me/theorems/dff9daf9-83e9-4401-bd4b-c80c87737e09
-- title:
--   Ends: while Step
-- statement:
--   A loop whose test holds: one round, then the loop again.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L123-L127
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Logic.lean#L123-L127

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

theorem Light.Ends.whileStep {σ c s T} {Q : State → Prop} (T₁ T₂ : ℕ) (hs : c.Safe lim σ) (hc : c.Holds σ)
    (h : Ends lim P d s σ T₁ fun σ' => Ends lim P d (.while c s) σ' T₂ Q)
    (hT : c.cost + 1 + T₁ + T₂ ≤ T) : Ends lim P d (.while c s) σ T Q := by sorry
