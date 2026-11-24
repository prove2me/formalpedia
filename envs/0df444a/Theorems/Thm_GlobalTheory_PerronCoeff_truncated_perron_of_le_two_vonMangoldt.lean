-- Prove2me | Theorems.Thm_GlobalTheory_PerronCoeff_truncated_perron_of_le_two_vonMangoldt
-- name    : GlobalTheory.PerronCoeff.truncated_perron_of_le_two_vonMangoldt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:43:59.98146+00:00
-- url     : https://prove2.me/theorems/6aa216a4-8396-4fce-9502-8bd9c9c5943e
-- title:
--   Perron Coeff: truncated perron of le two von Mangoldt
-- statement:
--   The Perron Coeff construction uses the truncated perron of le two von Mangoldt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronOfLeTwoVonMangoldt.lean#L9-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronOfLeTwoVonMangoldt.lean#L9-L157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronOfLeTwoVonMangoldt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.PerronCoeff
open GlobalTheory.PerronPsi

theorem GlobalTheory.PerronCoeff.truncated_perron_of_le_two_vonMangoldt : ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (u T : ℝ), (∀ n, ‖c n‖ ≤ 2 * Λ n) → 2 ≤ T → T ≤ u → ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n) - (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, LSeries c (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)‖ ≤ C * (u * Real.log u ^ 2 / T + Real.log u) := by sorry
