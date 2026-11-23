-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_policyIterNum_spec
-- name    : Mdp.DiscountedMDP.policyIterNum_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:40:03.40302+00:00
-- url     : https://prove2.me/theorems/2bf03e24-024e-4822-b962-66876da092be
-- title:
--   Discounted MDP: policy Iter Num spec
-- statement:
--   The Discounted MDP construction uses the policy Iter Num spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/PolicyIteration.lean#L280-L282
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/PolicyIteration.lean#L280-L282

import Definitions.Def_Mdp_ValueIteration
import Definitions.Def_Mdp_PolicyIteration
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.policyIterNum_spec (d : S → A) :
    M.policyStep ((M.policyStep)^[M.policyIterNum d] d) = (M.policyStep)^[M.policyIterNum d] d := by sorry
