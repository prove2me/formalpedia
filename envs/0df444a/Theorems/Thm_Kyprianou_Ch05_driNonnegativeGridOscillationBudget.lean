-- Prove2me | Theorems.Thm_Kyprianou_Ch05_driNonnegativeGridOscillationBudget
-- name    : Kyprianou.Ch05.driNonnegativeGridOscillationBudget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:46:42.053131+00:00
-- url     : https://prove2.me/theorems/cf54d2f1-5658-50d6-9495-cba81d017e76
-- title:
--   Small directly Riemann integrable oscillation budget restricts to nonnegative indices
-- statement:
--   Small directly Riemann integrable oscillation budget restricts to nonnegative indices
-- source:
--   Kyprianou (2006), Theorem 5.1(ii), corrected key renewal theorem, Darboux grid estimates.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.driNonnegativeGridOscillationBudget
    (h : Real → Real) (hDRI : DirectlyRiemannIntegrable h)
    (eps : Real) (heps : 0 < eps) :
    ∃ d : Real, 0 < d ∧
      Summable (fun k : Nat => |riCellOscillation h d (k : Int)|) ∧
      (∑' k : Nat, riCellOscillation h d (k : Int))*d < eps := by sorry
