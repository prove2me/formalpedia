-- Prove2me | Theorems.Thm_Kyprianou_Ch05_gridAverageSeries
-- name    : Kyprianou.Ch05.gridAverageSeries
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:46:39.346076+00:00
-- url     : https://prove2.me/theorems/c0f26895-afe5-5521-90b7-364a87b8c566
-- title:
--   Integrable function has absolutely summable grid cell averages and correct total
-- statement:
--   Integrable function has absolutely summable grid cell averages and correct total
-- source:
--   Kyprianou (2006), Theorem 5.1(ii), corrected key renewal theorem, Darboux grid estimates.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.gridAverageSeries
    (h : Real → Real) (hi : Integrable h)
    (d : Real) (hd : 0 < d) :
    let c := fun k : Nat =>
      (∫ z in Set.Ico ((k : Real)*d) (((k : Real)+1)*d), h z ∂volume)/d
    Summable (fun k => |c k|) ∧
      (∑' k : Nat, c k)*d = (∫ y in Set.Ici 0, h y ∂volume) := by sorry
