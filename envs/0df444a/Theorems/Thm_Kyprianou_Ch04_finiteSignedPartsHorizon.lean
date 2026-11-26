-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteSignedPartsHorizon
-- name    : Kyprianou.Ch04.finiteSignedPartsHorizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:15:52.991042+00:00
-- url     : https://prove2.me/theorems/e144cae9-6025-47d7-bedc-e4592bd9ab97
-- title:
--   finiteSignedPartsHorizon
-- statement:
--   Finite expected absolute compensator mass bounds both signed-part masses.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite expected absolute compensator mass bounds both signed-part masses. -/
theorem Kyprianou.Ch04.finiteSignedPartsHorizon {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (nu : Measure ℝ) (k : ℝ → ℝ → Omega → ℝ)
    (t : NNReal)
    (hFin : (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal |k s x w| ∂nu ∂volume ∂P) < ⊤) :
    (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (max (k s x w) 0) ∂nu ∂volume ∂P) < ⊤ ∧
    (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (max (-k s x w) 0) ∂nu ∂volume ∂P) < ⊤ := by
  sorry
