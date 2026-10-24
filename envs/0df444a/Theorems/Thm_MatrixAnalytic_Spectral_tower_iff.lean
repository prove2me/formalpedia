-- Prove2me | Theorems.Thm_MatrixAnalytic_Spectral_tower_iff
-- name    : MatrixAnalytic.Spectral.tower_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:17.728758+00:00
-- url     : https://prove2.me/theorems/811746f7-d082-4b68-bf68-8bb0d49400fa
-- title:
--   Theorem 9.4.2 — towers (Jordan chains) of G from Γ(λ) and Γ⁽¹⁾(λ)
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and finitely many phases; assume $P$ stochastic and irreducible, $A = A_0 + A_1 + A_2$ irreducible, and the QBD positive recurrent. Let $G$ be its first-passage matrix, $\lambda$ an eigenvalue of $G$, $p \ge 1$, and $v_1, \dots, v_p$ complex column vectors with $v_1 \ne 0$. Then $v_p, v_{p-1}, \dots, v_1$ are in a tower for $G$ relative to $\lambda$ (that is, $(\lambda I - G)v_1 = 0$ and $v_i = (\lambda I - G)v_{i+1}$ for $1 \le i \le p-1$) if and only if
--   $$\begin{aligned}\Gamma(\lambda)v_1 &= 0,\\ \Gamma(\lambda)v_2 &= \Gamma^{(1)}(\lambda)v_1 \quad (\text{if } p \ge 2),\\ \Gamma(\lambda)v_{i+1} &= \Gamma^{(1)}(\lambda)v_i - A_0v_{i-1}, \qquad 2 \le i \le p-1,\end{aligned}$$
--   where $\Gamma(x) = x^2A_0 + x(A_1 - I) + A_2$ and $\Gamma^{(1)}(x) = 2xA_0 + A_1 - I$.
--
--   Since the columns of a Jordan basis of $G$ are formed by towers, this determines the whole Jordan structure of $G$ from the blocks of the transition matrix.
--
--   **Formalization Note** Vectors are a function `v : ℕ → ι → ℂ` of which only $v_1, \dots, v_p$ are used. The book's tower starts from an eigenvector, so $v_1 \ne 0$ is a hypothesis of the equivalence (without it, $v_1 = 0$ and $v_2$ an eigenvector satisfy the equations but are not in a tower; finding F1). $\lambda$ ranges over the eigenvalues of $G$, the only values for which towers are defined.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 214 (towers) and p. 215, Theorem 9.4.2

import Mathlib
import Definitions.Def_MatrixAnalytic_Spectral_Chain
import Definitions.Def_MatrixAnalytic_Spectral_QBD
import Definitions.Def_MatrixAnalytic_Spectral_Polynomial

open scoped ENNReal
open Polynomial Matrix

namespace MatrixAnalytic.Spectral

/-- Theorem 9.4.2 (p. 215). For a positive recurrent irreducible QBD (6.1) with finitely many
phases and `A = A₀ + A₁ + A₂` irreducible, let `λ` be an eigenvalue of the first-passage matrix
`G`, `p ≥ 1`, and `v₁, …, v_p` column vectors with `v₁ ≠ 0`. Then `v_p, …, v₁` are in a tower
for `G` relative to `λ` if and only if `Γ(λ)v₁ = 0`, `Γ(λ)v₂ = Γ⁽¹⁾(λ)v₁` (when `p ≥ 2`), and
`Γ(λ)v_{i+1} = Γ⁽¹⁾(λ)v_i − A₀v_{i−1}` for `2 ≤ i ≤ p − 1`, where `Γ(x) = x²A₀ + x(A₁ − I) + A₂`
and `Γ⁽¹⁾(x) = 2xA₀ + A₁ − I`. -/
theorem tower_iff {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hA : IrreducibleC (matA A₀ A₁ A₂))
    (hpos : IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂))
    (lam : ℂ) (hlam : (matGc (qbdP B A₀ A₁ A₂)).charpoly.IsRoot lam)
    (p : ℕ) (hp : 1 ≤ p) (v : ℕ → ι → ℂ) (hv : v 1 ≠ 0) :
    InTower (matGc (qbdP B A₀ A₁ A₂)) lam p v ↔
      (GammaAt A₀ A₁ A₂ lam *ᵥ v 1 = 0 ∧
        (2 ≤ p → GammaAt A₀ A₁ A₂ lam *ᵥ v 2 = Gamma1At A₀ A₁ lam *ᵥ v 1) ∧
        ∀ i : ℕ, 2 ≤ i → i + 1 ≤ p →
          GammaAt A₀ A₁ A₂ lam *ᵥ v (i + 1) =
            Gamma1At A₀ A₁ lam *ᵥ v i - cMat A₀ *ᵥ v (i - 1))
      := by sorry

end MatrixAnalytic.Spectral
