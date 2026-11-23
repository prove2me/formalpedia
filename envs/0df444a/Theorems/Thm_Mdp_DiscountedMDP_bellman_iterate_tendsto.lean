-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_bellman_iterate_tendsto
-- name    : Mdp.DiscountedMDP.bellman_iterate_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:33:02.872036+00:00
-- url     : https://prove2.me/theorems/f8a2474e-b68d-49d5-ad3f-0d9ac98e8af3
-- title:
--   Discounted MDP: bellman iterate tendsto
-- statement:
--   Iterating `bellman` from *any* starting value function converges to `vOpt`. This is the
--       mathematical content behind value iteration's correctness — the Isabelle side proves the same
--       fact as `dist_\<L>\<^sub>b_tendsto` and leans on it directly in `Value_Iteration.thy`'s
--       termination argument. Here it falls straight out of `ContractingWith.tendsto_iterate_fixedPoint`
--       applied to `contractingWith_bellman`; no new proof content.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L81-L83
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L81-L83

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.bellman_iterate_tendsto (v : S → ℝ) :
    Filter.Tendsto (fun n => M.bellman^[n] v) Filter.atTop (nhds M.vOpt) := by sorry
