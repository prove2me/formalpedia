-- Prove2me | Theorems.Thm_OptimalAffinity_stationaryY_steady_of_nonneg
-- name    : OptimalAffinity.stationaryY_steady_of_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:03:40.793957+00:00
-- url     : https://prove2.me/theorems/7e1faa27-bb67-5991-ad95-614cf1a98811
-- title:
--   Optimal Affinity: stationary Y steady of nonneg
-- statement:
--   The Optimal Affinity construction uses the stationary Y steady of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean#L52-L66
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean#L52-L66

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section

theorem OptimalAffinity.stationaryY_steady_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    YSteady oa2x2 x (stationaryY x) := by sorry
