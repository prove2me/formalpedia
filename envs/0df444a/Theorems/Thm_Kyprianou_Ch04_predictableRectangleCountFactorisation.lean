-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableRectangleCountFactorisation
-- name    : Kyprianou.Ch04.predictableRectangleCountFactorisation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:14:45.953508+00:00
-- url     : https://prove2.me/theorems/d6ab6a79-9c72-4d09-a014-0c7279b32085
-- title:
--   Poisson count factorisation against a past event
-- statement:
--   Future independence gives the product of the expected count and event probability, with no finite-count restriction. The existing Poisson first-moment identity evaluates the expected count.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Expected Poisson count weighted by a past event. -/
theorem predictableRectangleCountFactorisation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N) :
    ∀ (u v : NNReal) (B : Set Real) (A : Set Omega),
      u ≤ v → MeasurableSet B → MeasurableSet[F u] A →
      (∫⁻ omega, N.N omega (Set.Ioc (u : Real) (v : Real) ×ˢ B) *
        A.indicator (fun _ => (1 : ENNReal)) omega ∂P) =
      referenceIntensity levyMeasure (Set.Ioc (u : Real) (v : Real) ×ˢ B) * P A := by
  sorry
end Kyprianou.Ch04
