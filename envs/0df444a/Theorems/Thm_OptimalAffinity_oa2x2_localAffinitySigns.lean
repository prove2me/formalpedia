-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_localAffinitySigns
-- name    : OptimalAffinity.oa2x2_localAffinitySigns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:57:58.206662+00:00
-- url     : https://prove2.me/theorems/98628e2d-537f-4158-bb0b-daeaa23b4bc3
-- title:
--   Optimal Affinity: oa2x2 local Affinity Signs
-- statement:
--   The Optimal Affinity construction uses the oa2x2 local Affinity Signs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Affinity.lean#L14-L17
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Affinity.lean#L14-L17

module
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Definitions.Def_proofs_OptimalAffinity_Affinity
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.oa2x2_localAffinitySigns :
    1 < forwardFlux oa2x2 0 1 1 / reverseFlux oa2x2 0 1 1 ∧
    1 < forwardFlux oa2x2 1 1 1 / reverseFlux oa2x2 1 1 1 := by sorry
