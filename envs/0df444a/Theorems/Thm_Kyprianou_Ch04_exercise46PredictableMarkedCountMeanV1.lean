-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46PredictableMarkedCountMeanV1
-- name    : Kyprianou.Ch04.exercise46PredictableMarkedCountMeanV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:36:50.322507+00:00
-- url     : https://prove2.me/theorems/0b88ce95-df66-4023-8195-08703e6f4ac6
-- title:
--   Expected physical marked count on a predictable compact-horizon set
-- statement:
--   Evaluate the already established full-horizon physical marked compensator equality on the predictable rectangle and rewrite the kernel evaluation as the selected count.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46PredictableMarkedCountMeanV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (T : NNReal)
    (E : Set (NNReal × Omega)) (hE : MeasurableSet[G.rightCont.predictable] E)
    (hT : ∀ p ∈ E, p.1 ≤ T)
    (B : Set Real) (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : Real)) :
    let NX : Omega → Measure (NNReal × Real) := fun w =>
      ((Measure.count.restrict {u : NNReal | 0 < u ∧ L.X u w -
        Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
        (fun u => (u,L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
    (∫⁻ w, NX w {p | (p.1,w) ∈ E ∧ p.2 ∈ B} ∂P) =
      ((((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal).prod P) E *
        L.ν B := by
  sorry
