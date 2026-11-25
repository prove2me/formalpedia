-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_oneWayFluxes
-- name    : OptimalAffinity.oa2x2_oneWayFluxes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:57:01.028698+00:00
-- url     : https://prove2.me/theorems/273a7f8d-534d-4596-93e0-562745f86efd
-- title:
--   Optimal Affinity: oa2x2 one Way Fluxes
-- statement:
--   The Optimal Affinity construction uses the oa2x2 one Way Fluxes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Steady.lean#L9-L14
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Steady.lean#L9-L14

module
public import Definitions.Def_proofs_OptimalAffinity_Source
public import Definitions.Def_proofs_OptimalAffinity_Steady
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_oneWayFluxes (x y : ℝ) :
    forwardFlux oa2x2 0 x y = 3 * x ∧
    reverseFlux oa2x2 0 x y = 2 * y ∧
    forwardFlux oa2x2 1 x y = 7 * y ^ 2 ∧
    reverseFlux oa2x2 1 x y = 6 * x ^ 2 * y := by sorry
