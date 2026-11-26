-- Prove2me | Theorems.Thm_FriedCrossing_Scale_resolvent_identity
-- name    : FriedCrossing.Scale.resolvent_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:38:04.380249+00:00
-- url     : https://prove2.me/theorems/9f157adf-f35a-4bc9-ba42-5c1150136356
-- title:
--   Scale: resolvent identity
-- statement:
--   THE RESOLVENT IDENTITY (CDDP (4.12)), derived from the inverse relations:
--   incl (R x − R y) = R x (B y − B x) R y as maps H (n+1) → H n.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L48-L55
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L48-L55

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

theorem FriedCrossing.Scale.resolvent_identity (n : ℕ) (x y : X) :
    (S.incl (n + 1) n (Nat.le_succ n)).comp (F.R (n + 1) x - F.R (n + 1) y) =
      ((F.R n x).comp (F.B n y - F.B n x)).comp (F.R (n + 1) y) := by sorry
