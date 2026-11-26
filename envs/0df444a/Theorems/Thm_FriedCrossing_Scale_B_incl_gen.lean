-- Prove2me | Theorems.Thm_FriedCrossing_Scale_B_incl_gen
-- name    : FriedCrossing.Scale.B_incl_gen
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:37:50.532137+00:00
-- url     : https://prove2.me/theorems/44ec5986-56d9-532a-8632-de09a24fc6bd
-- title:
--   Scale: B incl gen
-- statement:
--   The generator commutes with every inclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L75-L87
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L75-L87

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

theorem FriedCrossing.Scale.B_incl_gen (a b : ℕ) (hab : b ≤ a) (x : X) :
    (S.incl a b hab).comp (F.B a x) = (F.B b x).comp (S.incl (a + 1) (b + 1) (by omega)) := by sorry
