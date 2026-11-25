-- Prove2me | Theorems.Thm_Kyprianou_Ch04_sameTimeWeightedPoissonBoxCrossZero
-- name    : Kyprianou.Ch04.sameTimeWeightedPoissonBoxCrossZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:58:42.911803+00:00
-- url     : https://prove2.me/theorems/56016b12-1e6a-4356-abad-0c7701277ef6
-- title:
--   Signed past-weight orthogonality for disjoint marks in a common time interval
-- statement:
--   The cross moment of two compensated counts on disjoint mark sets in a common future interval, multiplied by an integrable past-measurable signed weight, is zero. No joint independence between the two counts and the filtration is assumed.
-- source:
--   Kyprianou Chapter 4 Exercise 4.4; count additivity and signed-weight polarisation.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_pastWeightedPoissonBoxSquareMoment
import Theorems.Thm_Kyprianou_Ch04_compensatedDisjointUnionAE
import Theorems.Thm_Kyprianou_Ch04_signedWeightSquarePolarization
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.sameTimeWeightedPoissonBoxCrossZero
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (u t : NNReal) (hut : u ≤ t)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hd : Disjoint A B)
    (hAfin : referenceIntensity ν (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ A) ≠ ⊤)
    (hBfin : referenceIntensity ν (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤)
    (W : Ω → ℝ) (hW : StronglyMeasurable[F u] W) (hWi : Integrable W P) :
    (∫ ω, W ω * N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ A) ω *
      N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ω ∂P) = 0 := by
  sorry
