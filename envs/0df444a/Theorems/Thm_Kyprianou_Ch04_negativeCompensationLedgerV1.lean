-- Prove2me | Theorems.Thm_Kyprianou_Ch04_negativeCompensationLedgerV1
-- name    : Kyprianou.Ch04.negativeCompensationLedgerV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:00:15.539808+00:00
-- url     : https://prove2.me/theorems/ac01c2b0-b198-4365-9e7a-4f44decef42b
-- title:
--   Integrable negative-jump compensation and pointwise ledger
-- statement:
--   For a measure supported by negative reals with finite truncated first moment, the small-jump linear compensation is integrable and adding it to the compensated characteristic kernel gives the uncompensated kernel almost everywhere.
-- source:
--   Supporting same-space triplet identification for Kyprianou (2006), Chapter 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_AvramDividend_Classical_boundedVariation_min_one_abs_integrable
open MeasureTheory ProbabilityTheory Set Complex AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.negativeCompensationLedgerV1 (ν : Measure ℝ)
    (hn : ∀ᵐ y ∂ν, y < 0)
    (hint : Integrable (fun y : ℝ => min 1 |y|) ν)
    (ξ : ℝ) :
    let l : ℝ → ℝ := (Ioo (-1 : ℝ) 0).indicator id
    Integrable (fun y => (l y : ℂ) * (ξ : ℂ) * I) ν ∧
      (fun y : ℝ => Complex.exp (I * ((ξ * y : ℝ) : ℂ)) - 1) =ᵐ[ν]
        (fun y => levyCompensatedIntegrand ξ y + (l y : ℂ) * (ξ : ℂ) * I) := by
  sorry
