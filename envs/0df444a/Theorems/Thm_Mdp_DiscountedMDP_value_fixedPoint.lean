-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_value_fixedPoint
-- name    : Mdp.DiscountedMDP.value_fixedPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:32:18.851455+00:00
-- url     : https://prove2.me/theorems/9f24cd31-d734-4ed2-9514-d82f44074889
-- title:
--   Discounted MDP: value fixed Point
-- statement:
--   The Discounted MDP construction uses the value fixed Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L134-L135
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L134-L135

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.value_fixedPoint (d : S → A) : M.Lpolicy d (M.value d) = M.value d := by sorry
