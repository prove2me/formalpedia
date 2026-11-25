-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_optimumOneWayFluxes
-- name    : OptimalAffinity.oa2x2_optimumOneWayFluxes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:57:24.974184+00:00
-- url     : https://prove2.me/theorems/82b4b24f-9aba-53e3-a921-457d26c5092f
-- title:
--   Optimal Affinity: oa2x2 optimum One Way Fluxes
-- statement:
--   The Optimal Affinity construction uses the oa2x2 optimum One Way Fluxes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Affinity.lean#L9-L12
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Affinity.lean#L9-L12

module
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Definitions.Def_proofs_OptimalAffinity_Affinity
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_optimumOneWayFluxes :
    forwardFlux oa2x2 0 1 1 = 3 ∧ reverseFlux oa2x2 0 1 1 = 2 ∧
    forwardFlux oa2x2 1 1 1 = 7 ∧ reverseFlux oa2x2 1 1 1 = 6 := by sorry
