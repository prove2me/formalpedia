-- Prove2me | Theorems.Thm_FriedCrossing_Scale_R_incl_gen
-- name    : FriedCrossing.Scale.R_incl_gen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:37:49.887798+00:00
-- url     : https://prove2.me/theorems/803a0825-6491-5b8f-bc01-7bd65c678518
-- title:
--   Scale: R incl gen
-- statement:
--   The resolvent commutes with every inclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L60-L72
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L60-L72

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

theorem FriedCrossing.Scale.R_incl_gen (a b : ℕ) (hab : b ≤ a) (x : X) :
    (S.incl a b hab).comp (F.R a x) = (F.R b x).comp (S.incl a b hab) := by sorry
