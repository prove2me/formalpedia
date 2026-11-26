-- Prove2me | Theorems.Thm_FriedCrossing_Scale_fderiv_B_incl_gen
-- name    : FriedCrossing.Scale.fderiv_B_incl_gen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:51:54.016008+00:00
-- url     : https://prove2.me/theorems/2d1d11df-3cc9-5552-9f89-f0004629f1f0
-- title:
--   Scale: fderiv B incl gen
-- statement:
--   The differentiated compatibility: incl a b ∘ ∂B a x h = ∂B b x h ∘ incl (a+1) (b+1).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L244-L266
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L244-L266

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

theorem FriedCrossing.Scale.fderiv_B_incl_gen (a b : ℕ) (hab : b ≤ a) (x h : X) :
    (S.incl a b hab).comp (fderiv ℝ (F.B a) x h) =
      (fderiv ℝ (F.B b) x h).comp (S.incl (a + 1) (b + 1) (by omega)) := by sorry
