-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_restricted_dirac_abs_integral_bound
-- name    : Kyprianou.Ch04.ito43_restricted_dirac_abs_integral_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:31:24.550045+00:00
-- url     : https://prove2.me/theorems/285fae18-7bb2-44d8-a268-c0c1f66ca6be
-- title:
--   Restricted countable atomic integrability from bounded absolute finite sums
-- statement:
--   Restricted countable atomic integrability from bounded absolute finite sums.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

/-- Absolute finite-sum bounds give integrability and an integral bound on a countable restricted atomic measure. -/

theorem Kyprianou.Ch04.ito43_restricted_dirac_abs_integral_bound {I : Type} [Countable I] (φ : I → ℝ × ℝ)
    (B : Set (ℝ × ℝ)) (hB : MeasurableSet B) (F : ℝ × ℝ → ℝ) (C : ℝ)
    (hfin : ∀ S : Finset I, (∑ s ∈ S, |B.indicator F (φ s)|) ≤ C) :
    IntegrableOn F B (Measure.sum fun s : I => Measure.dirac (φ s)) ∧
      |∫ z in B, F z ∂(Measure.sum fun s : I => Measure.dirac (φ s))| ≤ C := by sorry
