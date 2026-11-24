-- Prove2me | Theorems.Thm_GlobalTheory_PerronPsi_truncated_perron_psi
-- name    : GlobalTheory.PerronPsi.truncated_perron_psi
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:25.430979+00:00
-- url     : https://prove2.me/theorems/e76f8fc5-3e29-4369-ba1a-f3caaafc699e
-- title:
--   Perron Psi: truncated perron psi
-- statement:
--   The Perron Psi construction uses the truncated perron psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L436-L606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedPerronPsi.lean#L436-L606

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronPsi

theorem GlobalTheory.PerronPsi.truncated_perron_psi : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (u T : ℝ), 2 ≤ T → T ≤ 2 * u → 2 ≤ u → ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (Λ n : ℂ) * χ (n : ZMod q)) - (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, -(deriv (LFunction χ) ((1 + 1 / Real.log u : ℝ) + t * I) / LFunction χ ((1 + 1 / Real.log u : ℝ) + t * I)) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / ((1 + 1 / Real.log u : ℝ) + t * I)‖ ≤ C * (u * Real.log u ^ 2 / T + Real.log u) := by sorry
