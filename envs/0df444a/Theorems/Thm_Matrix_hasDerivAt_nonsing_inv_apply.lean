-- Prove2me | Theorems.Thm_Matrix_hasDerivAt_nonsing_inv_apply
-- name    : Matrix.hasDerivAt_nonsing_inv_apply
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T08:44:33.445186+00:00
-- url     : https://prove2.me/theorems/c6d9a5a6-a2ec-4fec-8908-12f220948ada
-- title:
--   Derivative of the inverse of a matrix path, entrywise
-- statement:
--   Let $M:\mathbb{R}\to\mathbb{C}^{n\times n}$ be a path of complex matrices whose entries are all differentiable at $t$, with entrywise derivative $M'$. Suppose $M(t)$ is invertible. Then every entry of $s\mapsto M(s)^{-1}$ is differentiable at $t$, and
--   $$\frac{d}{ds}\Big|_{s=t}M(s)^{-1}=-M(t)^{-1}\,M'\,M(t)^{-1}.$$
--   Only invertibility at the single point $t$ is assumed. Differentiability comes from Cramer's rule $M^{-1}=(\det M)^{-1}\operatorname{adj}M$. The value comes from differentiating $M(s)M(s)^{-1}=I$, which holds near $t$ because $\det M$ is continuous.
-- source:
--   Standard matrix calculus (derivative of the matrix inverse); entrywise form used for the positive unitary path of Hofer–Wysocki–Zehnder, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, proof of Theorem 3.4.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped ComplexOrder

theorem Matrix.hasDerivAt_nonsing_inv_apply {n : Type*} [Fintype n] [DecidableEq n]
    {M : ℝ → Matrix n n ℂ} {M' : Matrix n n ℂ} {t : ℝ}
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) t) (ht : (M t).det ≠ 0) (i j : n) :
    HasDerivAt (fun s => (M s)⁻¹ i j) ((-((M t)⁻¹ * M' * (M t)⁻¹)) i j) t := by sorry
