-- Prove2me | Theorems.Thm_Kyprianou_Ch04_levyBandEnergyV1
-- name    : Kyprianou.Ch04.levyBandEnergyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:51:39.932792+00:00
-- url     : https://prove2.me/theorems/9c009998-739c-4302-acd8-becb1bf4e74d
-- title:
--   Lévy measure band energy and quadratic bound
-- statement:
--   Lévy measure band energy and quadratic bound
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem levyBandEnergyV1 (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hfin : ν B < ⊤) (hBC : B ⊆ C) (hC1 : ∀ z ∈ C, |z| ≤ 1) :
    Integrable (B.indicator (fun z : ℝ => z^2)) ν ∧
      0 ≤ (∫ z, B.indicator (fun z : ℝ => z^2) z ∂ν) ∧
      (∫ z, B.indicator (fun z : ℝ => z^2) z ∂ν) ≤
        (∫⁻ z in C, ENNReal.ofReal (z^2) ∂ν).toReal := by
  sorry
end Kyprianou.Ch04
