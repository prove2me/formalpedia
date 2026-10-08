-- Prove2me | Theorems.Thm_Matrix_PosDef_map_ofReal
-- name    : Matrix.PosDef.map_ofReal
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T08:44:31.616963+00:00
-- url     : https://prove2.me/theorems/6421e4ff-6541-4a97-b5c3-ce12f26858fa
-- title:
--   A real positive definite matrix is positive definite over $\mathbb{C}$
-- statement:
--   Let $M$ be a real symmetric positive definite $n\times n$ matrix. Then $M$, viewed as a complex matrix, is Hermitian positive definite: $z^*Mz>0$ for every nonzero $z\in\mathbb{C}^n$.
--   Writing $z=u+iv$ with $u,v\in\mathbb{R}^n$, symmetry gives $z^*Mz=u^{\mathsf T}Mu+v^{\mathsf T}Mv$, and at least one of $u,v$ is nonzero.
-- source:
--   Standard linear algebra (complexification of a real inner product).

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped ComplexOrder

theorem Matrix.PosDef.map_ofReal {n : Type*} [Fintype n] {M : Matrix n n ℝ} (hM : M.PosDef) :
    (M.map (fun x : ℝ => (x : ℂ))).PosDef := by sorry
