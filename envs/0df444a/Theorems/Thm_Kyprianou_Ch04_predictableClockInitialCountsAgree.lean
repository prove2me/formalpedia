-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableClockInitialCountsAgree
-- name    : Kyprianou.Ch04.predictableClockInitialCountsAgree
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:03:41.616097+00:00
-- url     : https://prove2.me/theorems/fbe89507-4126-413c-8708-621bf8fee64b
-- title:
--   Initial predictable atom has zero expected raw and intensity count.
-- statement:
--   Initial predictable atom has zero expected raw and intensity count.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Weighted count agreement on the predictable generator. -/
theorem predictableClockInitialCountsAgree
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hRect : ∀ (u v : NNReal) (B : Set Real) (A : Set Omega),
      u ≤ v → MeasurableSet B → MeasurableSet[F u] A →
      (∫⁻ omega, N.N omega (Set.Ioc (u : Real) (v : Real) ×ˢ B) *
        A.indicator (fun _ => (1 : ENNReal)) omega ∂P) =
      referenceIntensity levyMeasure (Set.Ioc (u : Real) (v : Real) ×ˢ B) * P A)
    (t : NNReal) (B : Set Real) (hB : MeasurableSet B)
    (A : Set Omega) (C : Set Real) (hC : MeasurableSet C)
    (hA : MeasurableSet[F 0] A) :
    (∫⁻ w, N.N w ((Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' ({0} : Set NNReal)) ×ˢ
      (B ∩ C)) * A.indicator (fun _ => (1 : ENNReal)) w ∂P) =
    (∫⁻ w, referenceIntensity levyMeasure
      ((Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' ({0} : Set NNReal)) ×ˢ (B ∩ C)) *
      A.indicator (fun _ => (1 : ENNReal)) w ∂P) := by
  sorry
end Kyprianou.Ch04
