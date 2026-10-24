-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_det_of_rowwise_gaussian_integrality
-- name    : OAI.PiExponent.DeterminantContradiction.det_of_rowwise_gaussian_integrality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:09:53.93673+00:00
-- url     : https://prove2.me/theorems/fe614516-2c5a-4ce5-b474-76559e9270a9
-- title:
--   Combine row-wise Gaussian scales into a determinant scale
-- statement:
--   For a finite square complex matrix with Gaussian-integer row-scaled entries, the product of the row scales is a positive natural scale making the determinant a Gaussian integer, and its logarithm is bounded by the sum of the row-scale logarithms. This removes the determinant-expansion and scale-combination algebra from the parent. Prove it by factoring the product scale across rows in the determinant expansion, using that Gaussian integers are closed under sums and products, and applying the finite-product logarithm identity. Its hypotheses are supplied by the first child.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.det_of_rowwise_gaussian_integrality
    {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α Complex) (scale : α → Nat)
    (hscale_pos : ∀ i, 0 < scale i)
    (hscale_int : ∀ i j, ∃ a b : Int,
      (scale i : Complex) * M i j = (a : Complex) + Complex.I * (b : Complex))
    (B : Real)
    (hbudget : (∑ i : α, Real.log (scale i : Real)) ≤ B) :
    ∃ D : Nat, 0 < D ∧
      ∃ a b : Int,
        (D : Complex) * M.det = (a : Complex) + Complex.I * (b : Complex) ∧
          Real.log (D : Real) ≤ B := by
  sorry
