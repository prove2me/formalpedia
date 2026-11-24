-- Prove2me | Theorems.Thm_GlobalTheory_summable_shiftedLattice_normSq_rpow
-- name    : GlobalTheory.summable_shiftedLattice_normSq_rpow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:22:53.69551+00:00
-- url     : https://prove2.me/theorems/50dc0d65-5b06-42b6-b691-ab66d58599ca
-- title:
--   Global Theory: summable shifted Lattice norm Sq rpow
-- statement:
--   The Global Theory construction uses the summable shifted Lattice norm Sq rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeEpsteinZetaContinuation.lean#L11-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeEpsteinZetaContinuation.lean#L11-L41

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

theorem GlobalTheory.summable_shiftedLattice_normSq_rpow (w₁ w₂ x₀ : ℂ)
    (h : (starRingEnd ℂ w₁ * w₂).im ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : ℤ × ℤ => (‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) ^ (-σ) := by sorry
