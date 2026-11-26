-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46FirstMarkTruncatedCompensationV1
-- name    : Kyprianou.Ch04.exercise46FirstMarkTruncatedCompensationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:31:07.465737+00:00
-- url     : https://prove2.me/theorems/df198251-479e-4a91-93e5-6bde70cddc18
-- title:
--   First physical jump mark: truncated compensation identity
-- statement:
--   Probability of a first negative jump before the horizon with mark in B equals the common predictable-clock intensity factor times the Levy measure of B.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46FirstMarkTruncatedCompensationV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (hAm : Measurable A)
    (hFirst : ∀ᵐ w ∂P, A w = ((A w).untopD 0 : NNReal) ∧
      0 < (A w).untopD 0 ∧
      L.X ((A w).untopD 0) w <
        Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0) ∧
      ∀ u : NNReal, 0 < u → u < (A w).untopD 0 →
        L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u)
    (T : NNReal) (B : Set Real) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : Real)) :
    let a : Omega → NNReal := fun w => (A w).untopD 0
    let J : Omega → Real := fun w =>
      L.X (a w) w - Function.leftLim (fun u : NNReal => L.X u w) (a w)
    let E : Set (NNReal × Omega) :=
      {p | 0 < p.1 ∧ p.1 ≤ T ∧ (p.1 : WithTop NNReal) ≤ A p.2}
    P {w | A w ≤ (T : WithTop NNReal) ∧ J w ∈ B} =
      ((((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal).prod P) E *
        L.ν B := by
  sorry
