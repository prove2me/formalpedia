-- Prove2me | Theorems.Thm_Kyprianou_Ch05_measureEqOfFinitePositiveLaplace
-- name    : Kyprianou.Ch05.measureEqOfFinitePositiveLaplace
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T12:44:35.372059+00:00
-- url     : https://prove2.me/theorems/d6557a1e-7c2d-519a-b3e9-431480918fe4
-- title:
--   Uniqueness for measures with finite negative exponential transforms at all positive parameters
-- statement:
--   Two possibly infinite real measures whose negative exponential transforms agree and are finite for every positive parameter are equal. Tilt at parameter one, normalise the finite measures if nonzero, use probability Laplace uniqueness and remove the strictly positive tilt.
-- source:
--   Exponential tilting and Chapter 4 exercise46ProbabilityEqOfFiniteNegativeLaplaceV1.

import Mathlib
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.measureEqOfFinitePositiveLaplace
    (mu nu : Measure Real)
    (hfin : ∀ theta : Real, 0 < theta →
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂mu) < ⊤)
    (heq : ∀ theta : Real, 0 < theta →
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂mu) =
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂nu)) :
    mu = nu := by
  sorry
