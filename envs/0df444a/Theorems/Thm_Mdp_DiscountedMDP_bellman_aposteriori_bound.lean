-- Prove2me | Theorems.Thm_Mdp_DiscountedMDP_bellman_aposteriori_bound
-- name    : Mdp.DiscountedMDP.bellman_aposteriori_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:33:23.534807+00:00
-- url     : https://prove2.me/theorems/52ba008c-182e-4919-bcec-c73cf3a2ee44
-- title:
--   Discounted MDP: bellman aposteriori bound
-- statement:
--   A posteriori error bound: distance to `vOpt` after `n` iterations, bounded purely by how much
--       the *last* step moved — the "stop once consecutive iterates are close" criterion real
--       implementations use, and the shape `Value_Iteration.thy`'s `term_measure` is built from.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L95-L97
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Mdp/ValueIteration.lean#L95-L97

import Definitions.Def_Mdp_Basic
import Mathlib.Data.Finset.Max
import Definitions.Def_Mdp_ValueIteration
set_option autoImplicit true
open Mdp
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
open Mdp.DiscountedMDP
variable (M : DiscountedMDP S A)

theorem Mdp.DiscountedMDP.bellman_aposteriori_bound (v : S → ℝ) (n : ℕ) :
    dist (M.bellman^[n] v) M.vOpt ≤ dist (M.bellman^[n] v) (M.bellman^[n + 1] v) / (1 - M.lNN) := by sorry
