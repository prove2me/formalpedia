-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_policyStep_fixedPoint_value_eq_vOpt
-- name    : Mdp.DiscountedMDP.policyStep_fixedPoint_value_eq_vOpt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:40:18.606362+00:00
-- url     : https://prove2.me/theorems/7e463331-2608-400a-81e1-e10e5559b791
-- title:
--   Discounted MDP: policy Step fixed Point value eq v Opt
-- statement:
--   If `d` is already a fixed point of `policyStep`, its value function is already the global
--       optimum. Corresponds to the heart of `policy_iteration_correct` in `Policy_Iteration.thy`: a
--       policy admitting no further improvement has already-optimal value, because its value function
--       is then a fixed point of `bellman` itself — which, by Banach (Phase 2a's `vOpt`), has only
--       one.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/PolicyIteration.lean#L300-L308
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/PolicyIteration.lean#L300-L308

import Definitions.Def_Mdp_ValueIteration
import Definitions.Def_Mdp_PolicyIteration
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.policyStep_fixedPoint_value_eq_vOpt (d : S → A) (hd : M.policyStep d = d) :
    M.value d = M.vOpt := by sorry
