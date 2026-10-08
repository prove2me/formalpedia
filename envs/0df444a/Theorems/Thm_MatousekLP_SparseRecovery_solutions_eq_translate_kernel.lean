-- Prove2me | Theorems.Thm_MatousekLP_SparseRecovery_solutions_eq_translate_kernel
-- name    : MatousekLP.SparseRecovery.solutions_eq_translate_kernel
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:38:57.508449+00:00
-- url     : https://prove2.me/theorems/d03ee776-fede-43e8-ae40-912f2e88e441
-- title:
--   Proof of Lemma 8.5.4, p. 173 — the solution set of Ax = b is L + z
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $L=\{x\in\mathbb{R}^n: Ax=0\}$ its kernel, $b\in\mathbb{R}^m$, and let $z\in\mathbb{R}^n$ satisfy $Az=b$. Then the set of all solutions of $Ax=b$ is exactly the affine subspace $L+z$:
--   $$\{x\in\mathbb{R}^n: Ax=b\}=L+z=\{\ell+z:\ \ell\in L\}.$$
--
--   This step turns the uniqueness of the (BP) optimum into a statement about how the affine subspace $L+z$ meets an $\ell_1$-ball.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 173, proof of Lemma 8.5.4 ("the set of all solutions of Ax = b is exactly the affine subspace L + z")

import Mathlib
import Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit

namespace MatousekLP.SparseRecovery

open Matrix

/-- **Step in the proof of Lemma 8.5.4**, §8.5, p. 173, Matoušek & Gärtner, *Understanding and
Using Linear Programming*, Springer 2007: "the set of all solutions of `Ax = b` is exactly the
affine subspace `L + z`", where `L = {x : Ax = 0}` and `z` is a solution of `Ax = b`. -/
theorem solutions_eq_translate_kernel {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (z : Fin n → ℝ) (hz : A *ᵥ z = b) :
    {x : Fin n → ℝ | A *ᵥ x = b} = translate (kernel A) z := by sorry

end MatousekLP.SparseRecovery
