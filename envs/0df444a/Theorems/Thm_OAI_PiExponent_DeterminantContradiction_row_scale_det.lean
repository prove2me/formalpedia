-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_row_scale_det
-- name    : OAI.PiExponent.DeterminantContradiction.row_scale_det
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:19:42.829927+00:00
-- url     : https://prove2.me/theorems/3b9df303-e1e0-4e99-831e-ee9a46047202
-- title:
--   Factor row scales out of the determinant
-- statement:
--   Scaling row `i` by `scale i` scales the determinant by the product of all row scales. The local matrix is explicitly typed to avoid the field-notation elaboration failure; the identity needs no positivity assumption and includes the empty matrix case.

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.row_scale_det
    {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α Complex) (scale : α → Nat) :
    (let A : Matrix α α Complex := fun i j => (scale i : Complex) * M i j; A.det) =
      ((∏ i : α, scale i : Nat) : Complex) * M.det := by
  sorry
