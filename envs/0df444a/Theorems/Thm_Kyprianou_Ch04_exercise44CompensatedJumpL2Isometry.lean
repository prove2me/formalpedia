-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise44CompensatedJumpL2Isometry
-- name    : Kyprianou.Ch04.exercise44CompensatedJumpL2Isometry
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T22:27:55.037627+00:00
-- url     : https://prove2.me/theorems/2c7551b7-71b7-4942-a7af-afec388a727b
-- title:
--   Exercise 4.4: compensated Poisson-integral second-moment isometry
-- statement:
--   Under Theorem 4.4's nonanticipating predictable-integrand conditions, the first-moment integrability of Corollary 4.6 and finite expected time-integrated squared kernel, the compensated jump integral has second moment equal to the expected time-by-Levy-intensity integral of the squared kernel. No isometry or martingale conclusion is assumed.
-- source:
--   Kyprianou (2006), first edition, Chapter 4, Exercise 4.4(main), pp. 105-109.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Exercise 4.4 (p. 107). Second-moment isometry for the compensated jump integral. -/
theorem exercise44CompensatedJumpL2Isometry
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hL1 : forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) < ⊤)
    (hL2 : forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal ((phi s x omega) ^ 2) ∂levyMeasure)
          ∂volume) ∂P) < ⊤) :
    forall t : NNReal,
      (∫ omega,
        ((∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
            phi z.1 z.2 omega ∂(N.N omega)) -
          (∫ s in Set.Icc (0 : Real) (t : Real),
            (∫ x, phi s x omega ∂levyMeasure) ∂volume)) ^ 2 ∂P) =
      (∫ omega,
        (∫ s in Set.Icc (0 : Real) (t : Real),
          (∫ x, (phi s x omega) ^ 2 ∂levyMeasure)
          ∂volume) ∂P) := by
  sorry
end Kyprianou.Ch04
