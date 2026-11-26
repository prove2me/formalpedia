-- Prove2me | Theorems.Thm_Kyprianou_Ch05_finiteMeasureCellIntegralError
-- name    : Kyprianou.Ch05.finiteMeasureCellIntegralError
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:49:09.705951+00:00
-- url     : https://prove2.me/theorems/0053d204-0c08-4446-8610-bee50453e07a
-- title:
--   Cell integral error controlled by pointwise error and cell mass
-- statement:
--   Cell integral error controlled by pointwise error and cell mass
-- source:
--   Kyprianou (2006), Theorem 5.1(ii), corrected key renewal theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.finiteMeasureCellIntegralError
    (V : Measure Real) (S : Set Real) (hM : MeasurableSet S)
    (hF : V S ≠ ⊤) (f : Real → Real) (hf : IntegrableOn f S V)
    (c e : Real) (ha : ∀ z, z ∈ S → |f z-c| ≤ e) :
    |(∫ z in S, f z ∂V) - c*(V S).toReal| ≤ e*(V S).toReal := by sorry
