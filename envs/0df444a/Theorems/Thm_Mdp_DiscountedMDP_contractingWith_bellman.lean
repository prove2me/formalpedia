-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_contractingWith_bellman
-- name    : Mdp.DiscountedMDP.contractingWith_bellman
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:40:23.134939+00:00
-- url     : https://prove2.me/theorems/35c331f3-9719-4122-b9c7-c462a1129d4f
-- title:
--   Discounted MDP: contracting With bellman
-- statement:
--   The Bellman operator is a genuine contraction: Lipschitz with constant `< 1`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L193-L194
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/Basic.lean#L193-L194

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

theorem Mdp.DiscountedMDP.contractingWith_bellman : ContractingWith M.lNN M.bellman := by sorry
