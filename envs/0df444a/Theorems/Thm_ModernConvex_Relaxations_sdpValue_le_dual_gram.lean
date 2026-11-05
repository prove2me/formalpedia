-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_sdpValue_le_dual_gram
-- name    : ModernConvex.Relaxations.sdpValue_le_dual_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:10:08.728438+00:00
-- url     : https://prove2.me/theorems/fa2496de-914f-4e78-825a-b1fda1c766af
-- title:
--   MAXCUT SDP dual bound from an exact Gram certificate
-- statement:
--   **Weak duality for the Max-Cut SDP, in certificate form.** Let $a$ be a real matrix, $S$ the optimal value of $\max\{\tfrac14\sum_{i,j}a_{ij}(1-X_{ij}) : X\succeq0,\ X_{ii}=1\}$. Suppose $\lambda\in\mathbb R^n$ and a real matrix $B$ satisfy the exact identity
--   $$B^{\mathsf T}B = a+\operatorname{diag}\lambda .$$
--   Then
--   $$S\le\tfrac14\Big(\sum_{i,j}a_{ij}+\sum_i\lambda_i\Big).$$
--
--   The point of the Gram form is that both hypotheses are *checkable by finite arithmetic*: $B^{\mathsf T}B=a+\operatorname{diag}\lambda$ is an exact matrix identity, and positivity of $a+\operatorname{diag}\lambda$ then follows because a Gram matrix is positive semidefinite. A numerical solver can therefore emit rational $B$ and $\lambda$, and the resulting upper bound $\tfrac14(\sum_{i,j}a_{ij}+\sum_i\lambda_i)$ is a rational number, certified with no real arithmetic and no appeal to eigenvalue computation. Paired with a rational feasible $X$ whose objective is close to this bound, it gives a two-sided pin on $S$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, (4.3.15), p. 170; weak duality in the certificate form used by numerical SDP solvers.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **Weak duality with a rational Gram certificate.** If `λ` comes with an explicit matrix `B`
such that `Bᵀ B = a + diag λ`, then `(1/4)(Σ_{i,j} a_ij + Σ_i λ_i)` bounds the SDP value from
above. This is the form a numerical solver certifies: `B` is rational, the identity
`Bᵀ B = a + diag λ` is a finite rational identity, and the bound is then pure arithmetic. -/
theorem sdpValue_le_dual_gram {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : IsMaxcutSDPValue a S) (lam : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : Matrix.transpose B * B = a + Matrix.diagonal lam) :
    S ≤ (1 / 4) * ((∑ i, ∑ j, a i j) + ∑ i, lam i) := by sorry

end ModernConvex.Relaxations
