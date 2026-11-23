-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_policy_iteration_correct
-- name    : Mdp.DiscountedMDP.policy_iteration_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:40:34.335433+00:00
-- url     : https://prove2.me/theorems/b98a0114-bf52-4670-99b3-d0b51d11f11b
-- title:
--   Discounted MDP: policy iteration correct
-- statement:
--   **The final payoff.** Policy iteration, run from any starting policy, produces a policy whose
--       value is exactly optimal. Corresponds to `policy_iteration_correct` in
--       `Policy_Iteration.thy`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/PolicyIteration.lean#L313-L314
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/PolicyIteration.lean#L313-L314

import Definitions.Def_Mdp_ValueIteration
import Definitions.Def_Mdp_PolicyIteration
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.policy_iteration_correct (d : S → A) : M.value (M.policyIteration d) = M.vOpt := by sorry
