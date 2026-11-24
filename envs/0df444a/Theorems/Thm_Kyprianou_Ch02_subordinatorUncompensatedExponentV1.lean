-- Prove2me | Theorems.Thm_Kyprianou_Ch02_subordinatorUncompensatedExponentV1
-- name    : Kyprianou.Ch02.subordinatorUncompensatedExponentV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:41:03.82838+00:00
-- url     : https://prove2.me/theorems/ebb2adc9-7be3-4173-8f0c-3cec0fed0a90
-- title:
--   Rewrite positive-jump finite-variation characteristic exponent
-- statement:
--   Remove the Gaussian part and restrict the Lévy integral to positive marks; the zero atom is null. The truncated first moment makes the small-jump linear compensation integrable. Separate its integral and combine it with the original drift. The strict boundary at 1 is retained.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; sufficiency of the subordinator criterion.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.subordinatorUncompensatedExponentV1
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hs : ν (Set.Iio (0 : ℝ)) = 0) (hσ : σ = 0)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) (ξ : ℝ) :
    Kyprianou.Ch01.levyTripleExponent ⟨-a, σ ^ 2, ν, hν⟩ ξ =
      Complex.I * (((-a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂ν) * ξ : ℝ) : ℂ) +
      ∫ x in Set.Ioi (0 : ℝ),
        (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν := by
  sorry
