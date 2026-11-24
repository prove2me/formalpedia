-- Prove2me | Theorems.Thm_GlobalTheory_continuousOn_tsum_exp_neg_pi_mul
-- name    : GlobalTheory.continuousOn_tsum_exp_neg_pi_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:33.052312+00:00
-- url     : https://prove2.me/theorems/d0de3250-0696-400d-a55f-b8b2691a8984
-- title:
--   Global Theory: continuous On tsum exp neg pi mul
-- statement:
--   The Global Theory construction uses the continuous On tsum exp neg pi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeEpsteinZetaContinuation.lean#L60-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeEpsteinZetaContinuation.lean#L60-L73

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

theorem GlobalTheory.continuousOn_tsum_exp_neg_pi_mul {ι : Type*} {q : ι → ℝ} (hq : ∀ i, 0 < q i)
    (hs : Summable fun i => q i ^ (-(2 : ℝ))) :
    ContinuousOn (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) (Ioi 0) := by sorry
