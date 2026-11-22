-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_geometric_descending_potential
-- name    : Kyprianou.Ch08.StageB.source_result81_geometric_descending_potential
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:07:40.714126+00:00
-- url     : https://prove2.me/theorems/c216ff5a-6fa0-4e23-b97d-d34cc3dd9b6c
-- title:
--   Renewal potential with no atoms on the positive half-line
-- statement:
--   At any scale d>0, convolve the probability law with the geometric renewal measure for the kernel with density d ρ((x,∞)) on x>0, and multiply by d/f(d). The displayed drawdown law makes the kernel Laplace transform strictly below one and gives potential transform s/f(s). All the positive atoms of the resulting potential come from the leading drawdown term. Laplace uniqueness identifies the potentials at different scales, while the same drawdown equation at s=1 forces its mass on any fixed positive singleton to go to zero as d tends to infinity.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, tilted descending potential. Reduction of 4c63d0ad-20de-450a-9ecd-09b666951d4c.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_geometric_descending_potential
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (hdraw : ∀ d : ℝ, 0 < d → ∃ ρ : Measure ℝ,
      IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
          f d * (1 - s / d)) :
    ∃ ν : Measure ℝ, ν (Iio (0 : ℝ)) = 0 ∧
      (∀ x : ℝ, 0 ≤ x → ν (Iic x) < ⊤) ∧
      (∀ x : ℝ, 0 < x → ν {x} = 0) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) =
          ENNReal.ofReal (s / f s)) := by
  sorry
