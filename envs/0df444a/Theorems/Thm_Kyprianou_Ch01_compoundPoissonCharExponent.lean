-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonCharExponent
-- name    : Kyprianou.Ch01.compoundPoissonCharExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:55:49.88248+00:00
-- url     : https://prove2.me/theorems/34b458c3-d75e-4f5b-922a-8e0ac197e5fb
-- title:
--   §1.2.2 — compound Poisson characteristic exponent
-- statement:
--   Kyprianou §1.2.2, p. 6: the compound Poisson process with independent jumps and positive rate has a time-linear characteristic exponent with zero Gaussian component and Lévy measure equal to intensity times jump law. The precise driver assumptions are provided by LeanLevy's IsCompoundPoissonDriver. Editable draft, pending compilation. Every process, law and rate variable is explicitly quantified; compound Poisson exponent uses the direct compound-Poisson characteristic function instead of an unavailable triple exponent field.
-- source:
--   Kyprianou (2006), §1.2.2, pp. 5–7, equations (1.3) and associated compound Poisson exponent; LeanLevy, Processes/CompoundPoissonLaw.lean, frozen GitHub source commit 7e73fd9b23ad52956ec2756a815889a783131ce4.

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open MeasureTheory Filter Finset ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem Kyprianou.Ch01.compoundPoissonCharExponent
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν' : Measure ℝ) [IsProbabilityMeasure ν']
    (τ Y : ℕ → Ω → ℝ) (r : ℝ≥0)
    (hd : IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0)
    (b : ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (compoundPoisson b τ Y (t : ℝ))) ξ =
      Complex.exp (((t : ℝ) : ℂ) *
        (Complex.I * ((b * ξ : ℝ) : ℂ) +
          ((r : ℝ) : ℂ) * (charFun ν' ξ - 1))) := by
  sorry
