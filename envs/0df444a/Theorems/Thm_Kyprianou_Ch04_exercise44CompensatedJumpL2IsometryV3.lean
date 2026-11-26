-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise44CompensatedJumpL2IsometryV3
-- name    : Kyprianou.Ch04.exercise44CompensatedJumpL2IsometryV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:17:58.050636+00:00
-- url     : https://prove2.me/theorems/0452de7a-cdcc-4778-bc01-f3c1bc7ed169
-- title:
--   Exercise 4.4: compensated Poisson integral second-moment isometry (adapted Poisson measure)
-- statement:
--   The exact second-moment isometry for an admissible nonnegative predictable Poisson kernel with common-null left continuity, finite first and second compensator moments, and a Poisson random measure whose past evaluations are measurable relative to the filtration. The independent future and adapted past hypotheses together exclude anticipative-filtration cross-terms.
-- source:
--   Kyprianou (2006), Exercise 4.4, p. 107; corrected filtration hypothesis, consistent with the adapted Poisson measure used by the original martingale argument.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exercise 4.4 (p. 107). Second-moment isometry for the compensated jump integral. -/
theorem Kyprianou.Ch04.exercise44CompensatedJumpL2IsometryV3
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (hPast : forall (u : NNReal) (B : Set (Real × Real)),
      MeasurableSet B →
      B ⊆ Set.prod (Set.Icc (0 : Real) (u : Real)) Set.univ →
      Measurable[F u] (fun omega => N.N omega B))
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
