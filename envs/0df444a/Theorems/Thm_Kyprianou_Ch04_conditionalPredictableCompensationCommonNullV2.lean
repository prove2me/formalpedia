-- Prove2me | Theorems.Thm_Kyprianou_Ch04_conditionalPredictableCompensationCommonNullV2
-- name    : Kyprianou.Ch04.conditionalPredictableCompensationCommonNullV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:12:47.513329+00:00
-- url     : https://prove2.me/theorems/bf5da7d2-0e15-44ab-8e4a-28f5a74879e6
-- title:
--   Corollary 4.5: conditional predictable compensation (common null event correction)
-- statement:
--   Use one common almost-sure event for all marks and times. Apply corrected nonnegative compensation to the kernel multiplied by the past event and the indicator of the open-left future time interval.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.5, printed page 97.; correction of the formalisation of 368c2a96-9778-4fa8-b48f-154c83796c1b.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem conditionalPredictableCompensationCommonNullV2
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ omega ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (t : Real) (Set.Iio (t : Real)))
        (nhds (phi (t : Real) x omega))) :
    forall u t : NNReal, u <= t ->
      forall A : Set Omega, MeasurableSet[F u] A ->
      (∫⁻ omega in A,
        (∫⁻ z in Set.prod (Set.Ioc (u : Real) (t : Real)) Set.univ,
          ENNReal.ofReal (phi z.1 z.2 omega) ∂(N.N omega)) ∂P) =
      (∫⁻ omega in A,
        (∫⁻ s in Set.Ioc (u : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) := by
  sorry
end Kyprianou.Ch04
