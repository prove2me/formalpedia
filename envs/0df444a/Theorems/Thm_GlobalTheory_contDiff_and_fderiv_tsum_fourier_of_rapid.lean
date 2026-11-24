-- Prove2me | Theorems.Thm_GlobalTheory_contDiff_and_fderiv_tsum_fourier_of_rapid
-- name    : GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:45.531879+00:00
-- url     : https://prove2.me/theorems/11d9d80a-c3fa-4a60-9f02-0865b1300bae
-- title:
--   Global Theory: cont Diff and fderiv tsum fourier of rapid
-- statement:
--   The Global Theory construction uses the cont Diff and fderiv tsum fourier of rapid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean#L130-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean#L130-L167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open RapidFourier

theorem GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid :
    ∀ (n : ℕ) (c : (Fin n → ℤ) → ℂ), (∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C) → ContDiff ℝ ∞ (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) ∧ ∀ (x : Fin n → ℝ) (j : Fin n), fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) x (Pi.single j 1) = ∑' ν, 2 * π * I * (ν j : ℂ) * c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) := by sorry
