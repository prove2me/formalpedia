-- Prove2me | Theorems.Thm_FriedCrossing_Scale_one_le_lossBudget
-- name    : FriedCrossing.Scale.one_le_lossBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:37:58.232515+00:00
-- url     : https://prove2.me/theorems/645c87da-eb87-561f-b7b7-45894cf5fbbf
-- title:
--   Scale: one le loss Budget
-- statement:
--   The Scale construction uses the one le loss Budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L238-L241
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/resolvent_scale_9_11.lean#L238-L241

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

theorem FriedCrossing.Scale.one_le_lossBudget (k : ℕ) : 1 ≤ lossBudget k := by sorry
