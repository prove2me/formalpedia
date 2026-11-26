-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cutoffBandEnergiesV1
-- name    : Kyprianou.Ch04.cutoffBandEnergiesV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:00:05.165853+00:00
-- url     : https://prove2.me/theorems/fde093c1-27b2-56f6-89e4-aa17d07f6de1
-- title:
--   Integrability and quadratic energy bounds for nested cutoff bands
-- statement:
--   Integrability and quadratic energy bounds for nested cutoff bands
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem cutoffBandEnergiesV1 (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    let A : Set ℝ := {z | a < |z| ∧ |z| ≤ b ∧ |z| < 1}
    let B : Set ℝ := {z | b < |z| ∧ |z| < 1}
    let C : Set ℝ := {z | |z| ≤ b}
    let D : Set ℝ := {z | |z| < 1}
    (Integrable (A.indicator (fun z => z^2)) ν ∧
      0 ≤ ∫ z, A.indicator (fun z => z^2) z ∂ν ∧
      (∫ z, A.indicator (fun z => z^2) z ∂ν) ≤
        (∫⁻ z in C, ENNReal.ofReal (z^2) ∂ν).toReal) ∧
    (Integrable (B.indicator (fun z => z^2)) ν ∧
      0 ≤ ∫ z, B.indicator (fun z => z^2) z ∂ν ∧
      (∫ z, B.indicator (fun z => z^2) z ∂ν) ≤
        (∫⁻ z in D, ENNReal.ofReal (z^2) ∂ν).toReal) := by
  sorry
end Kyprianou.Ch04
