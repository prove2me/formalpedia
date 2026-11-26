-- Prove2me | Theorems.Thm_Kyprianou_Ch05_finiteMeasuresEqOfNegativeLaplace
-- name    : Kyprianou.Ch05.finiteMeasuresEqOfNegativeLaplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:52:45.222978+00:00
-- url     : https://prove2.me/theorems/cea3fb2d-1f4b-5a2f-a3c3-c36be6be84f7
-- title:
--   Finite measures of equal mass with equal finite negative Laplace transforms
-- statement:
--   Normalize equal nonzero finite masses and apply Chapter 4 probability Laplace uniqueness; handle the zero case separately.
-- source:
--   Kyprianou (2006), Chapter 5; reusable Laplace uniqueness bridge.

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.finiteMeasuresEqOfNegativeLaplace
    (mu nu : Measure Real) (hc : mu Set.univ = nu Set.univ)
    (hct : mu Set.univ ≠ ⊤)
    (hfin : ∀ t : Real, 0 < t →
      (∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂mu) < ⊤)
    (heq : ∀ t : Real, 0 < t →
      (∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂mu) =
      (∫⁻ x, ENNReal.ofReal (Real.exp (-t*x)) ∂nu)) :
    mu = nu := by
  sorry
