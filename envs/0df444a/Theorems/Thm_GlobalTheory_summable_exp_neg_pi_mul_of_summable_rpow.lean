-- Prove2me | Theorems.Thm_GlobalTheory_summable_exp_neg_pi_mul_of_summable_rpow
-- name    : GlobalTheory.summable_exp_neg_pi_mul_of_summable_rpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:15.001856+00:00
-- url     : https://prove2.me/theorems/30884860-fa5b-4c1f-9ecd-02f18d882a2f
-- title:
--   Global Theory: summable exp neg pi mul of summable rpow
-- statement:
--   The Global Theory construction uses the summable exp neg pi mul of summable rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeEpsteinZetaContinuation.lean#L43-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeEpsteinZetaContinuation.lean#L43-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptoticsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open GlobalTheory
open Set MeasureTheory
open scoped Topology

theorem GlobalTheory.summable_exp_neg_pi_mul_of_summable_rpow {ι : Type*} {q : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hs : Summable fun i => q i ^ (-(2 : ℝ))) {t : ℝ} (ht : 0 < t) :
    Summable fun i => Real.exp (-Real.pi * t * q i) := by sorry
