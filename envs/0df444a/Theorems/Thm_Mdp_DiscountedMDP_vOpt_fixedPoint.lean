-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_vOpt_fixedPoint
-- name    : Mdp.DiscountedMDP.vOpt_fixedPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:32:28.322662+00:00
-- url     : https://prove2.me/theorems/26685b59-5708-489b-b746-22bc3355f192
-- title:
--   Discounted MDP: v Opt fixed Point
-- statement:
--   `vOpt` really is a fixed point of `bellman`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L66-L67
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L66-L67

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.vOpt_fixedPoint : M.bellman M.vOpt = M.vOpt := by sorry
