-- Prove2me | Theorems.Thm_Matrix_abs_re_star_dotProduct_mulVec_le
-- name    : Matrix.abs_re_star_dotProduct_mulVec_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:21:08.670057+00:00
-- url     : https://prove2.me/theorems/08e4b197-49ee-4c71-af3a-ea8decfc8956
-- title:
--   Entrywise bound for the real part of a complex quadratic form
-- statement:
--   For a square complex matrix $D=(D_{ij})$ indexed by a finite type and any $x\in\mathbb C^n$,
--   $$|\operatorname{Re}(x^*Dx)|\le\Big(\sum_{i,j}|D_{ij}|\Big)\,\|x\|^2 .$$
--
--   Formalization Note: $x^*Dx$ is `star x ⬝ᵥ (D *ᵥ x)` and $\|x\|^2$ is `(star x ⬝ᵥ x).re`.
-- source:
--   Standard

import Mathlib

namespace Matrix

/-- For a square complex matrix `D` and a vector `x`,
`|Re (x* D x)| ≤ (∑ i, ∑ j, ‖D i j‖) · Re (x* x)`. -/
theorem abs_re_star_dotProduct_mulVec_le {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℂ) (x : n → ℂ) :
    |(star x ⬝ᵥ (D *ᵥ x)).re| ≤ (∑ i, ∑ j, ‖D i j‖) * (star x ⬝ᵥ x).re := by
  sorry

end Matrix
