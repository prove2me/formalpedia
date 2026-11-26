-- Prove2me | Theorems.Thm_FriedCrossing_Scale_derivLoss_apply
-- name    : FriedCrossing.Scale.derivLoss_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:38:06.523454+00:00
-- url     : https://prove2.me/theorems/509dad3e-e520-49aa-bb10-bc2358d86149
-- title:
--   Scale: deriv Loss apply
-- statement:
--   The Scale construction uses the deriv Loss apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L140-L144
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L140-L144

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

theorem FriedCrossing.Scale.derivLoss_apply (a b : ℕ) (hab : b + 2 ≤ a) (x : X) (h : X) :
    derivLoss F a b hab x h =
      -(((S.incl (b + 1) b (Nat.le_succ b)).comp (F.R (b + 1) x)).comp
        ((fderiv ℝ (F.B (b + 1)) x h).comp ((S.incl a (b + 2) hab).comp (F.R a x)))) := by sorry
