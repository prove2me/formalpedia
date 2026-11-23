-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_bellman_apriori_bound
-- name    : Mdp.DiscountedMDP.bellman_apriori_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:34:01.789173+00:00
-- url     : https://prove2.me/theorems/835a884d-edf7-45a2-b0ac-98647d51996a
-- title:
--   Discounted MDP: bellman apriori bound
-- statement:
--   A priori error bound: after `n` iterations from `v`, distance to `vOpt` is bounded by the
--       *first* step's movement, shrinking geometrically in `n`. Quantitative cousin of
--       `contraction_\<L>_dist` in `Value_Iteration.thy`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L88-L90
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L88-L90

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.bellman_apriori_bound (v : S → ℝ) (n : ℕ) :
    dist (M.bellman^[n] v) M.vOpt ≤ dist v (M.bellman v) * (M.lNN : ℝ) ^ n / (1 - M.lNN) := by sorry
