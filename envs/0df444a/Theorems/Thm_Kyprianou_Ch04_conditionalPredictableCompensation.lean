-- Prove2me | Theorems.Thm_Kyprianou_Ch04_conditionalPredictableCompensation
-- name    : Kyprianou.Ch04.conditionalPredictableCompensation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T22:23:58.933198+00:00
-- url     : https://prove2.me/theorems/368c2a96-9778-4fa8-b48f-154c83796c1b
-- title:
--   Corollary 4.5: conditional predictable compensation
-- statement:
--   The conditional expectation of raw Poisson jumps over (u,t] given F_u agrees with the conditional expectation of compensator intensity over that interval. It is represented equivalently by equal integrals over every event A in F_u, allowing extended nonnegative expectations and retaining all predictability hypotheses.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.5, printed page 97.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem conditionalPredictableCompensation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi) :
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
