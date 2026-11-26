-- Prove2me | Theorems.Thm_FriedCrossing_Scale_locallyLipschitz_loss_one
-- name    : FriedCrossing.Scale.locallyLipschitz_loss_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T04:38:05.340584+00:00
-- url     : https://prove2.me/theorems/cb1738bb-9d7d-4ac4-b25d-1c95fda22781
-- title:
--   Scale: locally Lipschitz loss one
-- statement:
--   Loss-one continuity (CDDP: "locally Lipschitz continuous in τ"):
--   x ↦ incl (n+1) n ∘ R (n+1) x.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L91-L116
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L91-L116

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

theorem FriedCrossing.Scale.locallyLipschitz_loss_one (n : ℕ) :
    LocallyLipschitz fun x => (S.incl (n + 1) n (Nat.le_succ n)).comp (F.R (n + 1) x) := by sorry
