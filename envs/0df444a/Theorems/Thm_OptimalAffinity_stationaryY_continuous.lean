-- Prove2me | Theorems.Thm_OptimalAffinity_stationaryY_continuous
-- name    : OptimalAffinity.stationaryY_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:04:00.377984+00:00
-- url     : https://prove2.me/theorems/32960184-f8cb-4e52-898e-a46233e65c20
-- title:
--   Optimal Affinity: stationary Y continuous
-- statement:
--   The Optimal Affinity construction uses the stationary Y continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean#L68-L70
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean#L68-L70

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section

theorem OptimalAffinity.stationaryY_continuous : Continuous stationaryY := by sorry
