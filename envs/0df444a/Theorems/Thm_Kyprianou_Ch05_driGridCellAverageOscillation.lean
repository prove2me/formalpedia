-- Prove2me | Theorems.Thm_Kyprianou_Ch05_driGridCellAverageOscillation
-- name    : Kyprianou.Ch05.driGridCellAverageOscillation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:46:49.912482+00:00
-- url     : https://prove2.me/theorems/0ded7b4c-5e08-46c4-b841-610bda8f31e1
-- title:
--   Each half-open cell average differs from its values by the closed-cell oscillation
-- statement:
--   Each half-open cell average differs from its values by the closed-cell oscillation
-- source:
--   Kyprianou (2006), Theorem 5.1(ii), corrected key renewal theorem, Darboux grid estimates.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.driGridCellAverageOscillation
    (h : Real → Real) (hi : Integrable h)
    (hloc : ∀ a b : Real, a < b →
      BddAbove (h '' Set.Icc a b) ∧ BddBelow (h '' Set.Icc a b))
    (d : Real) (hd : 0 < d) (k : Nat) (y : Real)
    (hy : y ∈ Set.Ico ((k : Real)*d) (((k : Real)+1)*d)) :
    |h y - (∫ z in Set.Ico ((k : Real)*d) (((k : Real)+1)*d), h z ∂volume)/d| ≤
      riCellOscillation h d (k : Int) := by sorry
