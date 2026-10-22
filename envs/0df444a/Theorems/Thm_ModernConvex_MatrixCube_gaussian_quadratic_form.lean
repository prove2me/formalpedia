-- Prove2me | Theorems.Thm_ModernConvex_MatrixCube_gaussian_quadratic_form
-- name    : ModernConvex.MatrixCube.gaussian_quadratic_form
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:50.913256+00:00
-- url     : https://prove2.me/theorems/c7ef1d5c-a30d-4473-9080-fb891c99e788
-- title:
--   Lemma 4.4.4 — E{ξᵀAξ} = Tr(A) and E{|ξᵀAξ|} ≥ ‖λ(A)‖₁/θ(Rank(A)) for ξ ∼ 𝒩(0, Iₙ)
-- statement:
--   Let $\xi\sim\mathcal N(0,I_n)$ be a standard Gaussian vector in $\mathbb R^n$, with density $p_n(u)=(2\pi)^{-n/2}\exp\{-u^Tu/2\}$, and let $A$ be a symmetric $n\times n$ matrix. Then
--   $$\text{(a)}\ \ \mathbf E\{\xi^TA\xi\}=\operatorname{Tr}(A),\qquad \text{(b)}\ \ \mathbf E\{|\xi^TA\xi|\}\ \ge\ \frac{1}{\theta(\operatorname{Rank}(A))}\,\|\lambda(A)\|_1 ,$$
--   where $\theta$ is the function (4.4.38) and $\|\lambda(A)\|_1$ is the sum of the absolute values of the eigenvalues of $A$.
--
--   Part (b) is the probabilistic step of the Matrix Cube Theorem: it converts the spectral quantity produced by duality into the expected violation along a random direction.
--
--   **Formalization Note** Expectations are written as Lebesgue integrals over $\mathbb R^n$ (`Fin n → ℝ`) against the density $p_n$. For $A=0$ the rank is $0$, $\theta(0)$ is a junk value, and both sides of (b) are $0$ ($\|\lambda(0)\|_1=0$), so the statement holds there regardless of that value.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 192, Lemma 4.4.4 (4.4.43)

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

open Matrix

namespace ModernConvex.MatrixCube

/-- Ben-Tal–Nemirovski, Lemma 4.4.4, p. 192, (4.4.43): with `ξ ∼ 𝒩(0, Iₙ)` (density
`pₙ(u) = (2π)^{−n/2} exp{−uᵀu/2}` on `ℝⁿ`), for every symmetric `n × n` matrix `A`
(a) `E{ξᵀAξ} = Tr(A)`,
(b) `E{|ξᵀAξ|} ≥ (1/θ(Rank(A))) ‖λ(A)‖₁`,
with `θ` the function of (4.4.38). Expectations are written as integrals against `pₙ` over
`ℝⁿ` with Lebesgue measure. -/
theorem gaussian_quadratic_form {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    ∫ u : Fin n → ℝ, (u ⬝ᵥ (A *ᵥ u)) * gaussDensity n u = A.trace ∧
    ∫ u : Fin n → ℝ, |u ⬝ᵥ (A *ᵥ u)| * gaussDensity n u ≥ 1 / theta A.rank * eigL1 A := by sorry

end ModernConvex.MatrixCube
