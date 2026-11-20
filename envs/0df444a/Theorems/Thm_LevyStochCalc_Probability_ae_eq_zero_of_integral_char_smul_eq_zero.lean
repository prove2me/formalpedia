-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_ae_eq_zero_of_integral_char_smul_eq_zero
-- name    : LevyStochCalc.Probability.ae_eq_zero_of_integral_char_smul_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:31:23.024243+00:00
-- url     : https://prove2.me/theorems/364c5782-3113-4970-a953-08710d847de3
-- title:
--   ae eq zero of integral char smul eq zero
-- statement:
--   The source theorem `LevyStochCalc.Probability.ae_eq_zero_of_integral_char_smul_eq_zero` is extracted from `LevyStochCalc.Probability.CharTotal`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_CharTotal_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Characters separate `L¹` densities

An integrable function on an inner-product space that integrates to zero against every character
`v ↦ exp(i⟪v, w⟫)` vanishes almost everywhere. Splitting the function into positive and negative
parts turns the hypothesis into an equality of the characteristic functions of two finite
measures, which `MeasureTheory.Measure.ext_of_charFun` reads as an equality of the measures.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal RealInnerProductSpace

namespace LevyStochCalc.Probability

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V]

theorem _root_.LevyStochCalc.Probability.ae_eq_zero_of_integral_char_smul_eq_zero {μ : Measure V} [IsFiniteMeasure μ]
    {u : V → ℝ} (hu : Integrable u μ)
    (h : ∀ w : V, ∫ v, u v • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) ∂μ = 0) :
    u =ᵐ[μ] 0 := by sorry
