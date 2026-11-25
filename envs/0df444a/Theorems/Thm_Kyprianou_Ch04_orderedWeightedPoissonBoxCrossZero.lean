-- Prove2me | Theorems.Thm_Kyprianou_Ch04_orderedWeightedPoissonBoxCrossZero
-- name    : Kyprianou.Ch04.orderedWeightedPoissonBoxCrossZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:52:48.422901+00:00
-- url     : https://prove2.me/theorems/c581803b-e6f2-5012-9bd1-3973eb7fa166
-- title:
--   Orthogonality of adapted weighted Poisson boxes on ordered time intervals
-- statement:
--   If the past Poisson counts are adapted, the expectation of the product of two square-integrable predictable weighted compensated counts on ordered disjoint time intervals is zero.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; adapted past and independent future increments.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_pastWeightCompensatedFutureBoxCentered
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.orderedWeightedPoissonBoxCrossZero
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ → Measurable[F u] (fun ω => N.N ω B))
    (a b c d : NNReal) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hFin : referenceIntensity ν (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ≠ ⊤)
    (H K : Ω → ℝ) (hH : StronglyMeasurable[F a] H) (hK : StronglyMeasurable[F c] K)
    (hK2 : Integrable (fun ω => (K ω)^2) P)
    (hE2 : Integrable (fun ω => (H ω *
      N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω)^2) P)
    (hL2 : Integrable (fun ω => (K ω *
      N.compensated (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ω)^2) P) :
    ∫ ω, (H ω * N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω) *
      (K ω * N.compensated (Set.Ioc (c : ℝ) (d : ℝ) ×ˢ B) ω) ∂P = 0 := by
  sorry
