-- Prove2me | Theorems.Thm_Kyprianou_Ch05_reflectedGridIntegralError
-- name    : Kyprianou.Ch05.reflectedGridIntegralError
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:27:14.733108+00:00
-- url     : https://prove2.me/theorems/d3e9836d-77f6-5461-816e-0aae9973eac6
-- title:
--   Bound the error of renewal convolution by reflected grid-cell oscillations
-- statement:
--   Bound the error of renewal convolution by reflected grid-cell oscillations
-- source:
--   Kyprianou (2006), Theorem 5.1(ii) corrected; grid averages and finite-partition error.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.reflectedGridIntegralError
    (V : Measure Real) (hfinite : ∀ x : Real, V (Set.Icc 0 x) ≠ ⊤)
    (h : Real → Real) (hm : Measurable h)
    (hloc : ∀ a b : Real, a < b →
      BddAbove (h '' Set.Icc a b) ∧ BddBelow (h '' Set.Icc a b))
    (d : Real) (hd : 0 < d) (c e : Nat → Real)
    (ha : ∀ (k : Nat) (y : Real), y ∈ Set.Ico ((k : Real)*d) (((k : Real)+1)*d) →
      |h y-c k| ≤ e k)
    (x : Real) (hx : 0 ≤ x) :
    |(∫ z in Set.Icc 0 x, h (x-z) ∂V) -
      (∑' k : Nat, c k * (V (Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d))).toReal)| ≤
      ∑' k : Nat, e k * (V (Set.Icc 0 x ∩ Set.Ioc (x-((k : Real)+1)*d) (x-(k : Real)*d))).toReal := by sorry
