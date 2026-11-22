-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_bellman_contracting
-- name    : Mdp.DiscountedMDP.bellman_contracting
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:52:48.043891+00:00
-- url     : https://prove2.me/theorems/f3dd45a5-fa80-4536-ac9e-3a01118434dd
-- title:
--   Discounted MDP: bellman contracting
-- statement:
--   **The theorem Phase 1 exists to port.** The Bellman operator is an `l`-Lipschitz contraction
--       in sup distance. Corresponds to `contraction_ℒ` in `MDP_reward.thy`:
--
--       `dist (\<L>\<^sub>b v) (\<L>\<^sub>b u) \<le> l * dist v u`
--
--       Built from `abs_sup'_sub_sup'_le` (sup is 1-Lipschitz) applied at each state, plus
--       `abs_expect_sub_le` (the transition step is `1`-Lipschitz, so scaling by `l` makes the whole
--       per-action term `l`-Lipschitz in `v`), then glued across states via `dist_pi_le_iff`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L166-L179
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L166-L179

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Definitions.Def_Mdp_Basic
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.bellman_contracting (v u : S → ℝ) :
    dist (M.bellman v) (M.bellman u) ≤ M.l * dist v u := by sorry
