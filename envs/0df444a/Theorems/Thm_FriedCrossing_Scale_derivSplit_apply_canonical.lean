-- Prove2me | Theorems.Thm_FriedCrossing_Scale_derivSplit_apply_canonical
-- name    : FriedCrossing.Scale.derivSplit_apply_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:52:05.943415+00:00
-- url     : https://prove2.me/theorems/d981a00e-de29-57fd-b906-29e49dc0b8cc
-- title:
--   Scale: deriv Split apply canonical
-- statement:
--   Every split equals the level-b canonical form −R b x ∘ ∂B b x h ∘ incl a (b+1) ∘ R a x.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L278-L288
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L278-L288

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

theorem FriedCrossing.Scale.derivSplit_apply_canonical (a b j : ℕ) (hj : b + j + 1 ≤ a) (x h : X) :
    derivSplit F a b j hj x h =
      -((F.R b x).comp ((fderiv ℝ (F.B b) x h).comp
        ((S.incl a (b + 1) (by omega)).comp (F.R a x)))) := by sorry
