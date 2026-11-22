-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_abs_expect_sub_le
-- name    : Mdp.DiscountedMDP.abs_expect_sub_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:02:41.174807+00:00
-- url     : https://prove2.me/theorems/21e9f837-fc9c-47cd-9991-b75a752162e7
-- title:
--   Discounted MDP: abs expect sub le
-- statement:
--   One step of `expect` moves `l`-scaled by at most `dist v u`: the PMF-weighted average of two
--       functions is within `dist v u` of each other, since the weights are nonnegative and sum to
--       `1` (`expect_kernel_sum_one`). Corresponds to non-expansiveness of `\<P>\<^sub>1 d` in the
--       Isabelle proof of `contraction_ℒ`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L138-L156
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L138-L156

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

theorem Mdp.DiscountedMDP.abs_expect_sub_le (s : S) (a : A) (v u : S → ℝ) :
    |M.expect s a v - M.expect s a u| ≤ dist v u := by sorry
