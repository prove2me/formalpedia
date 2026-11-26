-- Prove2me | Theorems.Thm_FriedCrossing_Scale_contDiff_derivSplit
-- name    : FriedCrossing.Scale.contDiff_derivSplit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:52:29.471809+00:00
-- url     : https://prove2.me/theorems/0313cea1-24bf-4b8d-b59f-98cddb3f754f
-- title:
--   Scale: cont Diff deriv Split
-- statement:
--   Smoothness of a split derivative from smoothness of its two resolvent factors.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L294-L305
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L294-L305

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_resolvent_scale_9_11
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
open FriedCrossing.Scale
universe u
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {S : BanachScale.{u}} (F : ResolventFamily S X)

theorem FriedCrossing.Scale.contDiff_derivSplit (k : ℕ) (a b j : ℕ) (hj : b + j + 1 ≤ a)
    (hU : ContDiff ℝ k fun x => (S.incl (b + j) b (Nat.le_add_right b j)).comp (F.R (b + j) x))
    (hV : ContDiff ℝ k fun x => (S.incl a (b + j + 1) hj).comp (F.R a x)) :
    ContDiff ℝ k fun x => derivSplit F a b j hj x := by sorry
