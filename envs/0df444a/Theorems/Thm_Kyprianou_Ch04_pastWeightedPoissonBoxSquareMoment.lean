-- Prove2me | Theorems.Thm_Kyprianou_Ch04_pastWeightedPoissonBoxSquareMoment
-- name    : Kyprianou.Ch04.pastWeightedPoissonBoxSquareMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:53:18.120511+00:00
-- url     : https://prove2.me/theorems/90779fd9-de96-5e4a-99a0-2c6682278d92
-- title:
--   Second moment of a compensated future box against an integrable past weight
-- statement:
--   For a finite-intensity future marked box, its compensated squared count multiplied by an integrable scalar past weight is integrable. The expectation factors as the intensity times the expectation of the weight.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; future-count independence and Poisson variance.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
import Theorems.Thm_Kyprianou_Ch04_pastWeightIndependentFutureCompensatedBox
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.pastWeightedPoissonBoxSquareMoment
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (u t : NNReal) (hut : u ≤ t) (B : Set ℝ) (hB : MeasurableSet B)
    (hFin : referenceIntensity ν (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤)
    (W : Ω → ℝ) (hW : StronglyMeasurable[F u] W) (hWi : Integrable W P) :
    Integrable (fun ω => W ω * (N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ω)^2) P ∧
    (∫ ω, W ω * (N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ω)^2 ∂P) =
      (∫ ω, W ω ∂P) * (referenceIntensity ν (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B)).toReal := by
  sorry
