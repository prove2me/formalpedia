-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nonnegativePredictableJumpCompensation
-- name    : Kyprianou.Ch04.nonnegativePredictableJumpCompensation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T22:23:30.809827+00:00
-- url     : https://prove2.me/theorems/12ced27e-522b-4bc8-a923-b6e95e2ac136
-- title:
--   Theorem 4.4: general nonnegative predictable jump compensation
-- statement:
--   For any nonnegative jointly measurable adapted left-continuous random time-space integrand and a Poisson random measure with nonanticipating filtration, the expected integral over [0,t] of the raw jump measure equals the expected time-by-Levy-intensity integral. Equality is in ENNReal, so infinite values are allowed.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.4, printed page 95.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem nonnegativePredictableJumpCompensation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi) :
    forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
          ENNReal.ofReal (phi z.1 z.2 omega) ∂(N.N omega)) ∂P) =
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) := by
  sorry
end Kyprianou.Ch04
