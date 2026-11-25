-- Prove2me | Theorems.Thm_OptimalAffinity_optimalAffinity_seedLowerBound_false
-- name    : OptimalAffinity.optimalAffinity_seedLowerBound_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:58:32.614166+00:00
-- url     : https://prove2.me/theorems/17ec20ee-6d41-5cfc-a792-544d9af4a3d9
-- title:
--   Optimal Affinity: optimal Affinity seed Lower Bound false
-- statement:
--   The Optimal Affinity construction uses the optimal Affinity seed Lower Bound false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Main.lean#L27-L30
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/Main.lean#L27-L30

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_Main
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity

theorem OptimalAffinity.optimalAffinity_seedLowerBound_false : ¬ TwoByTwoSeedLowerBound := by sorry
