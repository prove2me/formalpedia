-- Prove2me | Theorems.Thm_FriedCrossing_Scale_derivLoss_eq_derivSplit
-- name    : FriedCrossing.Scale.derivLoss_eq_derivSplit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:52:19.191185+00:00
-- url     : https://prove2.me/theorems/b8748299-5a70-5606-92f5-fa65d8f7a7e5
-- title:
--   Scale: deriv Loss eq deriv Split
-- statement:
--   The Scale construction uses the deriv Loss eq deriv Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L290-L291
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L290-L291

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

theorem FriedCrossing.Scale.derivLoss_eq_derivSplit (a b : ℕ) (hab : b + 2 ≤ a) (x : X) :
    derivLoss F a b hab x = derivSplit F a b 1 hab x := by sorry
