-- Prove2me | Theorems.Thm_OptimalAffinity_stationary_current_hasDerivAt_one
-- name    : OptimalAffinity.stationary_current_hasDerivAt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:04:04.043437+00:00
-- url     : https://prove2.me/theorems/4960426b-c400-4645-91b9-1bf0550beaf7
-- title:
--   Optimal Affinity: stationary current has Deriv At one
-- statement:
--   The Optimal Affinity construction uses the stationary current has Deriv At one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean#L79-L88
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean#L79-L88

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section

theorem OptimalAffinity.stationary_current_hasDerivAt_one :
    HasDerivAt
      (fun x => productionCurrent oa2x2 x (stationaryY x)) 0 1 := by sorry
