-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_policyIteration_isFixedPt
-- name    : Mdp.DiscountedMDP.policyIteration_isFixedPt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:40:16.779474+00:00
-- url     : https://prove2.me/theorems/c84b255c-b5e6-4d4a-b1be-ff82aafc92f9
-- title:
--   Discounted MDP: policy Iteration is Fixed Pt
-- statement:
--   `policyIteration d` really is a fixed point of `policyStep`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/PolicyIteration.lean#L291-L293
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/PolicyIteration.lean#L291-L293

import Definitions.Def_Mdp_ValueIteration
import Definitions.Def_Mdp_PolicyIteration
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.policyIteration_isFixedPt (d : S → A) :
    M.policyStep (M.policyIteration d) = M.policyIteration d := by sorry
