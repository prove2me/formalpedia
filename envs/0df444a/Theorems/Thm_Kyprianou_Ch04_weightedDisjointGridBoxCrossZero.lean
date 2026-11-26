-- Prove2me | Theorems.Thm_Kyprianou_Ch04_weightedDisjointGridBoxCrossZero
-- name    : Kyprianou.Ch04.weightedDisjointGridBoxCrossZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:03:38.165732+00:00
-- url     : https://prove2.me/theorems/19f120e9-f38d-4bbc-9f16-b058efe9aa84
-- title:
--   Weighted compensated cells in a disjoint time-mark grid have zero cross moment
-- statement:
--   Two predictable weighted compensated cells on ordered time intervals, or on disjoint marks in a common time interval, are orthogonal under the adapted-past and independent-future hypotheses.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; disjoint grid cell covariance.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_orderedWeightedPoissonBoxCrossZero
import Theorems.Thm_Kyprianou_Ch04_sameTimeWeightedPoissonBoxCrossZero
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.weightedDisjointGridBoxCrossZero
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ → Measurable[F u] (fun ω => N.N ω B))
    (a b c d : NNReal) (hab : a ≤ b) (hcd : c ≤ d)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAfin : referenceIntensity ν (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ≠ ⊤)
    (hBfin : referenceIntensity ν (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ≠ ⊤)
    (hGrid : b ≤ c ∨ d ≤ a ∨ (a = c ∧ b = d ∧ Disjoint A B))
    (H K : Ω → ℝ) (hH : StronglyMeasurable[F a] H) (hK : StronglyMeasurable[F c] K)
    (hH2 : Integrable (fun ω => (H ω)^2) P)
    (hK2 : Integrable (fun ω => (K ω)^2) P)
    (hE2 : Integrable (fun ω => (H ω *
      N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω)^2) P)
    (hL2 : Integrable (fun ω => (K ω *
      N.compensated (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ω)^2) P) :
    ∫ ω, (H ω * N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω) *
      (K ω * N.compensated (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ω) ∂P = 0 := by
  sorry
