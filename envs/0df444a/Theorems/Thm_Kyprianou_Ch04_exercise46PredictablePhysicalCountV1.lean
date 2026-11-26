-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46PredictablePhysicalCountV1
-- name    : Kyprianou.Ch04.exercise46PredictablePhysicalCountV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T23:29:52.026448+00:00
-- url     : https://prove2.me/theorems/426ea85c-fc28-5dbe-9552-4b64ebcf70d0
-- title:
--   Predictable physical marked count has the clock-intensity expectation
-- statement:
--   Use the full-horizon predictable marked compensator, evaluate it on the predictable time-path set times the negative mark set, and identify physical kernel sections by pushforward.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46PredictablePhysicalCountV1
    {Omega : Type} [mOmega : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal mOmega)
    (L : SpectrallyNegativeLevy P G)
    (T : NNReal) (hFinite : L.ν (Iio (0 : Real)) < ⊤)
    (E : Set (NNReal × Omega)) (hE : MeasurableSet[G.rightCont.predictable] E)
    (hBound : ∀ p ∈ E, p.1 ≤ T)
    (B : Set Real) (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : Real)) :
    let NX : Omega → Measure (NNReal × Real) := fun w =>
      ((Measure.count.restrict {u : NNReal |
        0 < u ∧ L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
        (fun u : NNReal => (u, L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
    (∫⁻ w, NX w {p : NNReal × Real | (p.1,w) ∈ E ∧ p.2 ∈ B} ∂P) =
      (((((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal).prod P) E) *
        L.ν B := by
  sorry
