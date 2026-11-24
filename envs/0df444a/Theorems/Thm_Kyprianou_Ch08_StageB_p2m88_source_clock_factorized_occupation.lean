-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_clock_factorized_occupation
-- name    : Kyprianou.Ch08.StageB.p2m88_source_clock_factorized_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:43:11.330807+00:00
-- url     : https://prove2.me/theorems/65d12978-be73-477c-8483-96664e5b2bf6
-- title:
--   Positive-discount occupation law through the Wiener–Hopf product clock
-- statement:
--   For the source spectrally negative process and positive discount q, its negative infimum at an independent rate-q exponential clock has a probability law on the nonnegative half-line with the CDF given by the one-sided exit formula. The actual killed occupation measure is 1/q times the mass of the stated event for independent exponential upward factor and negative-infimum factor.
-- source:
--   Kyprianou (2006), proof of Theorem 8.7, equations (8.20), (8.28), Corollary 8.8; printed pp. 224–226.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

namespace Kyprianou.Ch08.StageB

/-- Positive-discount occupation law through the Wiener–Hopf product clock -/
theorem p2m88_source_clock_factorized_occupation :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ q : ℝ, 0 < q →
      0 < Phi ψ q ∧
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Iio 0) = 0 ∧
        (∀ b : ℝ, 0 ≤ b → cdf ν b =
          q / Phi ψ q * W q b - q * ∫ s in (0 : ℝ)..b, W q s) ∧
        ∀ x : ℝ, 0 ≤ x → ∀ A : Set ℝ, MeasurableSet A →
          (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              tauMinus (shifted D.X x) 0 ω ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) =
          (ENNReal.ofReal q)⁻¹ *
            ((expMeasure (Phi ψ q)).prod ν)
              {z : ℝ × ℝ | z.2 ≤ x ∧ x + z.1 - z.2 ∈ A} := by
  sorry

end Kyprianou.Ch08.StageB
