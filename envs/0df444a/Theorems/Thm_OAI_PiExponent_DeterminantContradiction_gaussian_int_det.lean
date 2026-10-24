-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_gaussian_int_det
-- name    : OAI.PiExponent.DeterminantContradiction.gaussian_int_det
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:13:35.455215+00:00
-- url     : https://prove2.me/theorems/89386646-f4d9-4c38-8001-358c8246d7cd
-- title:
--   Determinants preserve Gaussian integrality
-- statement:
--   If every entry of a finite square complex matrix has integer real and imaginary parts, its determinant also has integer real and imaginary parts. This handles the determinant expansion's sums and products; the empty-index case gives determinant one.

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.gaussian_int_det
    {α : Type} [Fintype α] [DecidableEq α]
    (A : Matrix α α Complex)
    (hA : ∀ i j, ∃ a b : Int, A i j = (a : Complex) + Complex.I * (b : Complex)) :
    ∃ a b : Int, A.det = (a : Complex) + Complex.I * (b : Complex) := by
  sorry
