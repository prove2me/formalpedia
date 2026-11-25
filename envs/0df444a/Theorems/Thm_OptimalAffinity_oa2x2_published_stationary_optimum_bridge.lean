-- Prove2me | Theorems.Thm_OptimalAffinity_oa2x2_published_stationary_optimum_bridge
-- name    : OptimalAffinity.oa2x2_published_stationary_optimum_bridge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:04:08.093917+00:00
-- url     : https://prove2.me/theorems/531c596c-3e15-4516-b39a-421fd62aff97
-- title:
--   Optimal Affinity: oa2x2 published stationary optimum bridge
-- statement:
--   A positive local stationary branch through the global witness has a
--   finite zero current derivative and stays below the witness current.
--
--   Source: https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean#L92-L107
-- source:
--   https://github.com/mmislan/palomar-p004-optimal-affinity-counterexample/blob/50199f4bc2999fb43a0486dcb7571f9dfd333ff2/proofs/OptimalAffinity/SourceBridge.lean#L92-L107

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge
set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section

theorem OptimalAffinity.oa2x2_published_stationary_optimum_bridge :
    ∃ y : ℝ → ℝ,
      y 1 = 1 ∧
      HasDerivAt (fun x => productionCurrent oa2x2 x (y x)) 0 1 ∧
      ∀ᶠ x : ℝ in nhds 1,
        0 < x ∧ 0 < y x ∧ YSteady oa2x2 x (y x) ∧
          productionCurrent oa2x2 x (y x) ≤
            productionCurrent oa2x2 1 1 := by sorry
