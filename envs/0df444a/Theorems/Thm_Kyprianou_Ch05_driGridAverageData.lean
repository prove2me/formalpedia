-- Prove2me | Theorems.Thm_Kyprianou_Ch05_driGridAverageData
-- name    : Kyprianou.Ch05.driGridAverageData
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:27:12.573144+00:00
-- url     : https://prove2.me/theorems/c2e7ea6c-ce36-49c7-818b-eac29b0c5d7f
-- title:
--   Direct Riemann integrability yields summable grid averages and arbitrarily small oscillation budget
-- statement:
--   Direct Riemann integrability yields summable grid averages and arbitrarily small oscillation budget
-- source:
--   Kyprianou (2006), Theorem 5.1(ii) corrected; grid averages and finite-partition error.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.driGridAverageData
    (h : Real → Real) (hm : Measurable h)
    (hDRI : DirectlyRiemannIntegrable h) (eps : Real) (heps : 0 < eps) :
    ∃ d : Real, 0 < d ∧ ∃ c e : Nat → Real,
      Summable (fun k => |c k|) ∧ Summable (fun k => |e k|) ∧
      (∀ (k : Nat) (y : Real), y ∈ Set.Ico ((k : Real)*d) (((k : Real)+1)*d) →
        |h y-c k| ≤ e k) ∧
      (∑' k : Nat, c k)*d = (∫ y in Set.Ici 0, h y ∂volume) ∧
      (∑' k : Nat, e k)*d < eps := by sorry
