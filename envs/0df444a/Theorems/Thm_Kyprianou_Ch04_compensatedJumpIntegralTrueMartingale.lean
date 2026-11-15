-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compensatedJumpIntegralTrueMartingale
-- name    : Kyprianou.Ch04.compensatedJumpIntegralTrueMartingale
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T22:24:35.733195+00:00
-- url     : https://prove2.me/theorems/61a5bc8c-34e9-49c2-b76f-9c0e0650fed4
-- title:
--   Corollary 4.6: integrable compensated jump integral is a true martingale
-- statement:
--   Under the predictability and nonanticipation conditions of Theorem 4.4, with finite expected absolute compensator integral on each finite time horizon, the raw marked Poisson integral minus its time-by-intensity compensator is a genuine integrable P-martingale relative to F, not merely a local martingale.
-- source:
--   Kyprianou (2006), first edition, numbered result 4.6, printed page 97.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem compensatedJumpIntegralTrueMartingale
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hFinite : forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) < ⊤) :
    MeasureTheory.Martingale
      (fun (t : NNReal) omega =>
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
          phi z.1 z.2 omega ∂(N.N omega)) -
        (∫ s in Set.Icc (0 : Real) (t : Real),
          (∫ x, phi s x omega ∂levyMeasure) ∂volume))
      F P := by
  sorry
end Kyprianou.Ch04
