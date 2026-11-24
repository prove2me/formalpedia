-- Prove2me | Theorems.Thm_Kyprianou_Ch04_nonnegativePredictableJumpCompensationCommonNullV2
-- name    : Kyprianou.Ch04.nonnegativePredictableJumpCompensationCommonNullV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:03:17.532848+00:00
-- url     : https://prove2.me/theorems/f2db7765-bfc7-473d-afbb-6927e0eb67a4
-- title:
--   Theorem 4.4: general nonnegative predictable jump compensation (common null event correction)
-- statement:
--   Expected raw jump integral equals expected time-by-intensity integral in ENNReal. Retain all original hypotheses and require a single almost-sure event on which left-continuity holds at every positive time for every mark. Per-mark exceptional null events alone admit anticipating random-mark diagonals.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95; correction to formal predictable kernel hypothesis of 12ced27e-522b-4bc8-a923-b6e95e2ac136.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem nonnegativePredictableJumpCompensationCommonNullV2
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
