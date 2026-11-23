-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_numIters_spec
-- name    : Mdp.DiscountedMDP.numIters_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:39:01.005833+00:00
-- url     : https://prove2.me/theorems/672b0765-27e7-4ef6-b7ac-66f0824ab64d
-- title:
--   Discounted MDP: num Iters spec
-- statement:
--   The Discounted MDP construction uses the num Iters spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIterationAlgorithm.lean#L99-L101
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIterationAlgorithm.lean#L99-L101

import Definitions.Def_Mdp_ValueIteration
import Definitions.Def_Mdp_ValueIterationAlgorithm
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.numIters_spec {eps : ℝ} (heps : 0 < eps) (v : S → ℝ) :
    M.stopCond eps v (M.numIters heps v) := by sorry
