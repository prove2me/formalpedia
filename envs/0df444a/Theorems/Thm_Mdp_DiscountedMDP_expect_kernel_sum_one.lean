-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_expect_kernel_sum_one
-- name    : Mdp.DiscountedMDP.expect_kernel_sum_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:30:11.796715+00:00
-- url     : https://prove2.me/theorems/998bb5b1-ce52-44fc-bf71-c8e1a62cbd7a
-- title:
--   Discounted MDP: expect kernel sum one
-- statement:
--   The kernel really is a probability distribution once you convert its `ℝ≥0∞` masses to `ℝ`:
--       they still sum to `1`. Isolated as its own lemma because it's the one step in the contraction
--       proof that has to reach into `PMF`'s own API (`tsum_coe`) rather than pure `Finset`/`abs`
--       manipulation. `PMF.tsum_coe`, `tsum_fintype`, and `PMF.apply_ne_top` all confirmed by
--       `lake build`, as-named.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L126-L132
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L126-L132

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

theorem Mdp.DiscountedMDP.expect_kernel_sum_one (s : S) (a : A) :
    ∑ s' : S, (M.K s a s').toReal = 1 := by sorry
