-- Prove2me | Theorems.Thm_Kyprianou_Ch04_markedClockRectangleEval
-- name    : Kyprianou.Ch04.markedClockRectangleEval
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:54:26.515579+00:00
-- url     : https://prove2.me/theorems/5e8319fe-eb27-4457-98db-ebe92ef2881a
-- title:
--   Expected clock measure evaluation on a marked rectangle
-- statement:
--   Test the clock integral representation on the indicator of the marked rectangle. For a fixed sample, this indicator vanishes outside its sample event and otherwise restricts the time and mark coordinates.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem markedClockRectangleEval
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (R : Omega → Measure (Real × Real))
    (t : NNReal) (B : Set Real) (hB : MeasurableSet B)
    (M : @Measure ((NNReal × Omega) × Real) (F.predictable.prod inferInstance))
    (hM : ∀ f : ((NNReal × Omega) × Real) → ENNReal, Measurable[F.predictable.prod inferInstance] f →
      (∫⁻ p, f p ∂M) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
        f ((z.1.toNNReal, w), z.2) ∂(R w) ∂P))
    (D : Set NNReal) (hD : MeasurableSet D)
    (A : Set Omega) (C : Set Real) (hC : MeasurableSet C)
    (hDC : MeasurableSet[F.predictable.prod inferInstance] ((D ×ˢ A) ×ˢ C)) :
    M ((D ×ˢ A) ×ˢ C) =
      ∫⁻ w, R w ((Set.Icc (0 : Real) (t : Real) ∩ Real.toNNReal ⁻¹' D) ×ˢ (B ∩ C)) *
        A.indicator (fun _ => (1 : ENNReal)) w ∂P := by
  sorry
end Kyprianou.Ch04
