-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyGaussianZeroOfExponentialGridPowerLowerBoundV1
-- name    : Kyprianou.Ch02.levyGaussianZeroOfExponentialGridPowerLowerBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:46:44.810021+00:00
-- url     : https://prove2.me/theorems/7d09b7f7-9167-4069-b123-eae951e373a0
-- title:
--   Uniform exponential increment loss bound rules out a nonzero Gaussian coefficient
-- statement:
--   Under the exact source characteristic-triplet and Levy-process hypotheses, uniformly positive powers of the expected exponentially damped absolute increments at time 1/(n+1) force the Gaussian coefficient to vanish. The positive powers imply an O(1/(n+1)) bound on expected 1-exp(-abs increment). Compare the characteristic function at a frequency of order sqrt(n+1) with one using this loss; the Gaussian contribution to the modulus of the specified Levy-Khintchine characteristic function remains strictly below one if sigma is positive. This is a genuine analytic implication, not assuming bounded variation or the conclusion.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12, bounded-variation Lévy paths and Lévy-triplet characterisation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.levyGaussianZeroOfExponentialGridPowerLowerBoundV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ,
        c ≤ (∫ ω, Real.exp (-|X (((n : ℝ≥0) + 1)⁻¹) ω|) ∂P) ^ (n + 1)) →
    σ = 0 := by
  sorry
