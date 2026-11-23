-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_lipschitzWith_bellman
-- name    : Mdp.DiscountedMDP.lipschitzWith_bellman
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:30:48.574094+00:00
-- url     : https://prove2.me/theorems/f6c63930-fdde-4539-99d1-7fb8d5918db9
-- title:
--   Discounted MDP: lipschitz With bellman
-- statement:
--   `bellman_contracting` restated in the `LipschitzWith` vocabulary (`edist`-based, not
--       `dist`-based) that `ContractingWith` is built on. `LipschitzWith.of_dist_le_mul` is the
--       bridging lemma from the plain-`dist` inequality we already have to the official definition —
--       least certain name in this block, alongside `ContractingWith` itself.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L189-L190
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L189-L190

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

theorem Mdp.DiscountedMDP.lipschitzWith_bellman : LipschitzWith M.lNN M.bellman := by sorry
