-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise44CompensatedJumpL2IsometryV2
-- name    : Kyprianou.Ch04.exercise44CompensatedJumpL2IsometryV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T14:42:20.527418+00:00
-- url     : https://prove2.me/theorems/5444bfc4-7e21-43ff-a297-701168bb5e54
-- title:
--   Exercise 4.4: compensated jump L2 isometry (common null event)
-- statement:
--   Second moment isometry with common almost-sure left continuity in time.
-- source:
--   Kyprianou (2006), Exercise 4.4.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exercise 4.4 (p. 107). Second-moment isometry for the compensated jump integral. -/
theorem Kyprianou.Ch04.exercise44CompensatedJumpL2IsometryV2
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
        (nhds (phi (t : Real) x omega)))
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
