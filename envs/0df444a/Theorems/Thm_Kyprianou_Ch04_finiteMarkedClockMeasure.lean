-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteMarkedClockMeasure
-- name    : Kyprianou.Ch04.finiteMarkedClockMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:54:28.763836+00:00
-- url     : https://prove2.me/theorems/e384c9a4-1867-4115-b6c3-33b3eb07dc66
-- title:
--   Expected marked clock measure on the predictable sigma algebra
-- statement:
--   Restrict each random measure to the given rectangle, modify it to zero on the exceptional infinite-mass event, and push the resulting finite kernel onto time, sample and mark space. Bind with the probability measure and trim to the predictable product sigma algebra.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem finiteMarkedClockMeasure
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (R : Omega → Measure (Real × Real))
    (hR : ∀ S : Set (Real × Real), MeasurableSet S →
      Measurable (fun w => R w S))
    (t : NNReal) (B : Set Real) (hB : MeasurableSet B)
    (hFin : ∀ᵐ w ∂P, R w (Set.Icc (0 : Real) (t : Real) ×ˢ B) ≠ ⊤) :
    ∃ M : @Measure ((NNReal × Omega) × Real) (F.predictable.prod inferInstance),
      ∀ f : ((NNReal × Omega) × Real) → ENNReal, Measurable[F.predictable.prod inferInstance] f →
        AEMeasurable (fun w => ∫⁻ z in (Set.Icc (0 : Real) (t : Real) ×ˢ B),
          f ((z.1.toNNReal, w), z.2) ∂(R w)) P ∧
        (∫⁻ p, f p ∂M) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
        f ((z.1.toNNReal, w), z.2) ∂(R w) ∂P) := by
  sorry
end Kyprianou.Ch04
