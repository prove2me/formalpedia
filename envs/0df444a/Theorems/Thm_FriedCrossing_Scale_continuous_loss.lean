-- Prove2me | Theorems.Thm_FriedCrossing_Scale_continuous_loss
-- name    : FriedCrossing.Scale.continuous_loss
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:37:57.289425+00:00
-- url     : https://prove2.me/theorems/6e1cbbd3-f30b-5367-833e-bb5004c6969a
-- title:
--   Scale: continuous loss
-- statement:
--   Continuity with any loss ≥ 1, in the shape used downstream.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L119-L127
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L119-L127

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

theorem FriedCrossing.Scale.continuous_loss (a b : ℕ) (hab : b + 1 ≤ a) :
    Continuous fun x => (S.incl a b (by omega)).comp (F.R a x) := by sorry
