-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41GridRestartFactorV3
-- name    : Kyprianou.Ch04.exercise41GridRestartFactorV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:40:24.786039+00:00
-- url     : https://prove2.me/theorems/220731d4-3f85-4d5c-a97a-7e9cf09bc5ab
-- title:
--   Finite grid hit probability times slope-window probability is bounded by successful restart probability
-- statement:
--   For a finite grid of observations, construct measurable hit and successful restart events and prove the probability product lower bound.
-- source:
--   Kyprianou (2006), Exercise 4.1(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_exercise41GridFirstV2
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41GridRestartFactorV3
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (D R : Finset NNReal) (b δ : NNReal) (e : ℝ)
    (hD : ∀ t ∈ D, t ≤ b)
    (hR : ∀ u ∈ R, 0 < u ∧ u ≤ δ) :
    let C : NNReal → Set Ω := fun t => {ω | |L.X t ω| < e}
    let τ := exercise41GridFirstV2 D C b
    let A : Set Ω := {ω | ∃ t ∈ D, ω ∈ C t}
    let G : Set (NNReal → ℝ) :=
      {y | ∀ u ∈ R, L.drift / 2 * (u : ℝ) ≤ y u}
    let B := A ∩ {ω | (fun u => L.X (τ ω + u) ω - L.X (τ ω) ω) ∈ G}
    let p := P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
      L.drift / 2 * (u : ℝ) ≤ L.X u ω}
    MeasurableSet A ∧ MeasurableSet B ∧ p * P A ≤ P B  := by
  sorry
