-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finitePoissonIndicatorIntegralAE
-- name    : Kyprianou.Ch04.finitePoissonIndicatorIntegralAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:45:29.797167+00:00
-- url     : https://prove2.me/theorems/db3ef279-b0f3-4ebb-be1f-23b092da9873
-- title:
--   Almost-sure physical compensated Poisson integral formula for finite weighted indicators
-- statement:
--   The physical random-measure integral minus the reference intensity integral of a finite sum of random-weighted finite-intensity indicators equals the corresponding compensated count sum almost surely.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; finite predictable marked Poisson isometry.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch04_finiteWeightedIndicatorIntegral
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
universe u v w

theorem Kyprianou.Ch04.finitePoissonIndicatorIntegralAE
    {Ω : Type u} {E : Type v} {ι : Type w}
    [MeasurableSpace Ω] [MeasurableSpace E] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure E) [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    (s : Finset ι) (B : ι → Set (ℝ × E)) (H : ι → Ω → ℝ)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, referenceIntensity ν (B i) ≠ ⊤) :
    let K := fun ω z => ∑ i ∈ s, (B i).indicator (fun _ => H i ω) z
    ∀ᵐ ω ∂P, (∫ z, K ω z ∂(N.N ω)) -
      (∫ z, K ω z ∂referenceIntensity ν) =
      ∑ i ∈ s, H i ω * N.compensated (B i) ω := by
  sorry
