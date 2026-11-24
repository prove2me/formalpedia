-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SpecBound_norm_pow_le_of_eigenvalues_lt
-- name    : GlobalTheory.CompanionTheory.SpecBound.norm_pow_le_of_eigenvalues_lt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:43.211313+00:00
-- url     : https://prove2.me/theorems/f8d051d3-c793-421d-b21c-98cbf9cd56b1
-- title:
--   Spec Bound: norm pow le of eigenvalues lt
-- statement:
--   The Spec Bound construction uses the norm pow le of eigenvalues lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormPowLeOfEigenvaluesLt.lean#L8-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormPowLeOfEigenvaluesLt.lean#L8-L64

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormPowLeOfEigenvaluesLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped NNReal ENNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SpecBound

theorem GlobalTheory.CompanionTheory.SpecBound.norm_pow_le_of_eigenvalues_lt (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (T : W →L[ℂ] W) (ρ : ℝ)
    (h : ∀ μ : ℂ, Module.End.HasEigenvalue (T : Module.End ℂ W) μ → ‖μ‖ < ρ) :
    ∃ C : ℝ, ∀ j : ℕ, ‖T ^ j‖ ≤ C * ρ ^ j := by sorry
