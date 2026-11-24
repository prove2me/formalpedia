-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableCompensationFromRectangleCounts
-- name    : Kyprianou.Ch04.predictableCompensationFromRectangleCounts
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:14:49.922805+00:00
-- url     : https://prove2.me/theorems/116e50ef-bfb1-4ca7-b70f-c6d8b3d57954
-- title:
--   Extend predictable rectangle count identities to nonnegative integrands
-- statement:
--   Use the rectangle identities to identify the expected Poisson measure and reference intensity times probability on the predictable product sigma algebra. The initial-time slice has zero expected count by the Poisson first-moment identity. Extend by sigma-finite uniqueness, and integrate the measurable nonnegative kernel.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
/-- Extend predictable rectangle count identities to general nonnegative integrands. -/
theorem predictableCompensationFromRectangleCounts
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
    (psi : Real → Real → Omega → ENNReal)
    (hPsi : Measurable[F.predictable.prod inferInstance]
      (fun z : (NNReal × Omega) × Real => psi (z.1.1 : Real) z.2 z.1.2)) :
    ∀ t : NNReal,
      (∫⁻ omega, (∫⁻ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
        psi z.1 z.2 omega ∂(N.N omega)) ∂P) =
      (∫⁻ omega, (∫⁻ s in Set.Icc (0 : Real) (t : Real),
        (∫⁻ x, psi s x omega ∂levyMeasure) ∂volume) ∂P) := by
  sorry
end Kyprianou.Ch04
