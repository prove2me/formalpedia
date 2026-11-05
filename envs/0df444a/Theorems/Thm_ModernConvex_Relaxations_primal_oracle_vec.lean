-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_primal_oracle_vec
-- name    : ModernConvex.Relaxations.primal_oracle_vec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:40:42.865375+00:00
-- url     : https://prove2.me/theorems/9b7e1844-b204-4ae4-8cb0-335619125805
-- title:
--   Primal separation oracle in ellipsoid coordinates
-- statement:
--   **The primal separation oracle, in the coordinates an ellipsoid run uses.**
--
--   Let $x\in\mathbb R^{n^2}$ be the enumeration of a symmetric matrix. Then either that matrix is positive semidefinite, or there is a nonzero $w\in\mathbb R^{n^2}$ with
--   $$(y-x)\cdot w\le 0$$
--   for every $y$ that enumerates a positive semidefinite matrix.
--
--   The certificate is explicit: if the matrix is not positive semidefinite there is $v\in\mathbb R^n$ with $v^{\mathsf T}Xv<0$, and $w$ is the enumeration of $-vv^{\mathsf T}$. Then $(y-x)\cdot w=\langle Y-X,-vv^{\mathsf T}\rangle=v^{\mathsf T}Xv-v^{\mathsf T}Yv<0$ by the Frobenius-pairing identity, using $v^{\mathsf T}Yv\ge0$.
--
--   This is exactly the answer an ellipsoid run on the primal body $\{X\succeq0,\ X_{ii}=1\}$ consumes at an infeasible centre, stated on $\mathbb R^{n^2}$ with the coordinate dot product so that Bubeck's Theorem 2.4 applies verbatim.
-- source:
--   Ben-Tal & Nemirovski, (4.3.15), p. 170; the oracle consumed by Bubeck arXiv:1405.4980v2 Thm 2.4 on the primal MAXCUT body.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_MatrixVec

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- **The primal oracle in vector form.** For a symmetric matrix, reindexed as a vector of length
`n * n`, either it is positive semidefinite, or there is a nonzero vector `w` with
`(y - x) ⬝ᵥ w ≤ 0` for every positive semidefinite `y`. -/
theorem primal_oracle_vec {n : ℕ} (x : Fin (n * n) → ℝ) (hx : (finToMat x).IsHermitian) :
    (finToMat x).PosSemidef ∨
      ∃ w : Fin (n * n) → ℝ, w ≠ 0 ∧
        ∀ y : Fin (n * n) → ℝ, (finToMat y).PosSemidef → (y - x) ⬝ᵥ w ≤ 0 := by sorry

end ModernConvex.Relaxations
