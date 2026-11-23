-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_findPolicy_spec
-- name    : Mdp.DiscountedMDP.findPolicy_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:33:50.765257+00:00
-- url     : https://prove2.me/theorems/919297e0-b579-4b65-8dfc-88e084a67257
-- title:
--   Discounted MDP: find Policy spec
-- statement:
--   The Discounted MDP construction uses the find Policy spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L151-L154
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L151-L154

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.findPolicy_spec (v : S → ℝ) (s : S) (a' : A) :
    M.r s a' + M.l * M.expect s a' v
      ≤ M.r s (M.findPolicy v s) + M.l * M.expect s (M.findPolicy v s) v := by sorry
