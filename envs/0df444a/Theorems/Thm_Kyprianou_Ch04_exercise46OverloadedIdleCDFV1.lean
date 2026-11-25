-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46OverloadedIdleCDFV1
-- name    : Kyprianou.Ch04.exercise46OverloadedIdleCDFV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T09:54:45.221103+00:00
-- url     : https://prove2.me/theorems/3e0017d1-888d-541b-b8c6-b54eebf3760b
-- title:
--   Exercise 4.6(ii): overloaded idle-time CDF from Theorem 4.1
-- statement:
--   For unit drift and overloaded jump-magnitude intensity, total idle occupation of the zero-initial-workload queue is exponential with the positive maximal root of the Laplace exponent.
-- source:
--   Kyprianou (2006), Chapter 4 Exercise 4.6(ii), consequence of corrected Theorem 4.1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46OverloadedIdleCDFV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : L.drift = 1)
    (hrho : 1 < ∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) :
    ∃ phi : Real, 0 < phi ∧ L.ψ phi = 0 ∧
      (∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) ∧
      ∀ x : Real, 0 ≤ x →
        (P {omega : Omega |
          (∫⁻ t in Ici (0 : Real),
            if sSup ((fun s : NNReal => L.X s omega) '' Iic t.toNNReal) -
              L.X t.toNNReal omega = 0 then (1 : ENNReal) else 0 ∂volume)
            ≤ ENNReal.ofReal x}).toReal = 1 - Real.exp (-phi * x) := by
  sorry
