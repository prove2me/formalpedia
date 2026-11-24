-- Prove2me | Theorems.Thm_GlobalTheory_fourier_coeff_eq_zero_of_tsum_eq_zero_fin
-- name    : GlobalTheory.fourier_coeff_eq_zero_of_tsum_eq_zero_fin
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:53:23.021471+00:00
-- url     : https://prove2.me/theorems/506ed037-2c71-40c5-b189-b88c3364efb7
-- title:
--   Global Theory: fourier coeff eq zero of tsum eq zero fin
-- statement:
--   The Global Theory construction uses the fourier coeff eq zero of tsum eq zero fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FourierCoeffEqZeroOfTsumEqZeroFin.lean#L29-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FourierCoeffEqZeroOfTsumEqZeroFin.lean#L29-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffEqZeroOfHasSumMFourierOrthonormalImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FourierCoeffEqZeroOfTsumEqZeroFin
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
open Complex Matrix
open scoped ContDiff BigOperators Real

theorem GlobalTheory.fourier_coeff_eq_zero_of_tsum_eq_zero_fin :
    ∀ (n : ℕ) (c : (Fin n → ℤ) → ℂ), Summable (fun ν => ‖c ν‖) →
      (∀ x : Fin n → ℝ, ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = 0) →
      ∀ ν, c ν = 0 := by sorry
