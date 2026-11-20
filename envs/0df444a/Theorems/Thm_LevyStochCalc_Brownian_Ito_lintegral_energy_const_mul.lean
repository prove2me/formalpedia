-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_const_mul
-- name    : LevyStochCalc.Brownian.Ito.lintegral_energy_const_mul
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:00:55.560711+00:00
-- url     : https://prove2.me/theorems/ab9b6a22-6531-4b49-b1af-87032c9f5321
-- title:
--   lintegral energy const mul
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_energy_const_mul` is extracted from `LevyStochCalc.Brownian.ItoLinear`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Additivity of the L² Itô integral in the integrand

The Itô isometry and the isometry of differences determine every squared `L²`-distance among
`∫ H₁ dW`, `∫ H₂ dW` and `∫ (H₁ + H₂) dW` in terms of the energies of `H₁`, `H₂`, `H₁ + H₂` and
`H₁ − H₂`. The parallelogram law for those energies then forces
`∫ (H₁ + H₂) dW = ∫ H₁ dW + ∫ H₂ dW` almost everywhere.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Energy

variable {H₁ H₂ : Ω → ℝ → ℝ}

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_energy_const_mul {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (c T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ENNReal.ofReal (c ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
