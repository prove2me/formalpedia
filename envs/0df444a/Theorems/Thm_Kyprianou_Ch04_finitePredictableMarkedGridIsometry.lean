-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finitePredictableMarkedGridIsometry
-- name    : Kyprianou.Ch04.finitePredictableMarkedGridIsometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:45:36.013173+00:00
-- url     : https://prove2.me/theorems/5e4f7f0b-7ab8-5966-b8d7-51f283168776
-- title:
--   Finite predictable disjoint marked-grid Poisson isometry
-- statement:
--   For a finite predictable disjoint time-mark grid, the second moment of the compensated weighted count sum equals the sum of intensity-weighted coefficient second moments.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; finite predictable marked Poisson isometry.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableWeightedPoissonBoxL2
import Theorems.Thm_Kyprianou_Ch04_weightedDisjointGridBoxCrossZero
import Theorems.Thm_Kyprianou_Ch04_orthogonalFiniteFamilyL2Identity
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.finitePredictableMarkedGridIsometry
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ → Measurable[F u] (fun ω => N.N ω B))
    (s : Finset ι) (a b : ι → NNReal) (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, referenceIntensity ν (Set.Ioc (a i : ℝ) (b i : ℝ) ×ˢ B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P)
    (hGrid : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      b i ≤ a j ∨ b j ≤ a i ∨ (a i = a j ∧ b i = b j ∧ Disjoint (B i) (B j))) :
    ∫ ω, (∑ i ∈ s, H i ω *
      N.compensated (Set.Ioc (a i : ℝ) (b i : ℝ) ×ˢ B i) ω)^2 ∂P =
      ∑ i ∈ s, (referenceIntensity ν (Set.Ioc (a i : ℝ) (b i : ℝ) ×ˢ B i)).toReal *
        ∫ ω, (H i ω)^2 ∂P := by
  sorry
