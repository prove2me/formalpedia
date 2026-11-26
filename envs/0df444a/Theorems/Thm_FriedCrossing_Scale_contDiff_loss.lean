-- Prove2me | Theorems.Thm_FriedCrossing_Scale_contDiff_loss
-- name    : FriedCrossing.Scale.contDiff_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:52:17.539929+00:00
-- url     : https://prove2.me/theorems/50a3d6a5-4746-54b0-9503-9818780971a0
-- title:
--   Scale: cont Diff loss
-- statement:
--   THE THEOREM. On a scale with a locally uniformly bounded resolvent family and a smooth generator
--   family, the resolvent with loss ≥ L k is C^k in the parameter.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L309-L335
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L309-L335

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

theorem FriedCrossing.Scale.contDiff_loss : ∀ (k : ℕ) (a b : ℕ) (hab : b + lossBudget k ≤ a),
    ContDiff ℝ k fun x => (S.incl a b (le_trans (Nat.le_add_right b _) hab)).comp (F.R a x) := by sorry
