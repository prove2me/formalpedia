-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_bellman_eq_Lpolicy_findPolicy
-- name    : Mdp.DiscountedMDP.bellman_eq_Lpolicy_findPolicy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:34:03.301775+00:00
-- url     : https://prove2.me/theorems/27d867c5-20a6-4bbe-ba39-f183f4ea8637
-- title:
--   Discounted MDP: bellman eq Lpolicy find Policy
-- statement:
--   `findPolicy v` really does realise the `sup` in `bellman v` at every state: applying `Lpolicy`
--       with the greedy policy gives back exactly `bellman`. Corresponds to
--       `is_arg_max_find_policy` / `\<L>\<^sub>b_eq_argmax_L\<^sub>a` in `Value_Iteration.thy`, and is
--       the bridge that will let `vi_policy_opt`-style theorems (value iteration's extracted policy is
--       ε-optimal) transfer once `value_iteration` itself is ported.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L161-L168
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L161-L168

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.bellman_eq_Lpolicy_findPolicy (v : S → ℝ) (s : S) :
    M.bellman v s = M.Lpolicy (M.findPolicy v) v s := by sorry
