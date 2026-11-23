-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_valueIteration_error
-- name    : Mdp.DiscountedMDP.valueIteration_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:38:57.222658+00:00
-- url     : https://prove2.me/theorems/c6a200de-bff3-4645-ab39-c59921e54ca1
-- title:
--   Discounted MDP: value Iteration error
-- statement:
--   **The payoff.** Once `value_iteration` terminates (`eps > 0`), its output is within `eps / 2`
--       of optimal. Corresponds to `value_iteration_error` in `Value_Iteration.thy`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIterationAlgorithm.lean#L113-L144
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIterationAlgorithm.lean#L113-L144

import Definitions.Def_Mdp_ValueIteration
import Definitions.Def_Mdp_ValueIterationAlgorithm
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.valueIteration_error {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    2 * dist (M.valueIteration eps v) M.vOpt < eps := by sorry
