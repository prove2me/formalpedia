-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_exists_unique_fixedPoint_choose_eq_vOpt
-- name    : Mdp.DiscountedMDP.exists_unique_fixedPoint_choose_eq_vOpt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:33:55.10968+00:00
-- url     : https://prove2.me/theorems/853c7f00-d307-4140-8a9f-ce10b6c285c5
-- title:
--   Discounted MDP: exists unique fixed Point choose eq v Opt
-- statement:
--   `vOpt` and `Basic.lean`'s `exists_unique_fixedPoint` witness are the same value function: both
--       are *the* (unique) fixed point of `bellman`, just reached via different Mathlib entry
--       points.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L72-L74
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L72-L74

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration
import Theorems.Thm_Mdp_DiscountedMDP_exists_unique_fixedPoint

set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.exists_unique_fixedPoint_choose_eq_vOpt :
    M.exists_unique_fixedPoint.choose = M.vOpt := by sorry
