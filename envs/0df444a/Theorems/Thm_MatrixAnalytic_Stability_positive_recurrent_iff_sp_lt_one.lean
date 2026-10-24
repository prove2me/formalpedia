-- Prove2me | Theorems.Thm_MatrixAnalytic_Stability_positive_recurrent_iff_sp_lt_one
-- name    : MatrixAnalytic.Stability.positive_recurrent_iff_sp_lt_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:31.086904+00:00
-- url     : https://prove2.me/theorems/e14cc5cd-bd81-4701-9032-8903e2d20f73
-- title:
--   Corollary 7.1.2 — with finitely many phases, a QBD is positive recurrent iff sp(R) < 1
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and finitely many phases, and assume $P$ is stochastic and irreducible. Let $R$ be the rate matrix: $R_{ij}$ is the expected number of visits to $(1, j)$, starting from $(0, i)$, before the first return to $\ell(0)$. Then
--   $$\text{the QBD is positive recurrent} \iff \operatorname{sp}(R) < 1,$$
--   where $\operatorname{sp}(R)$ is the spectral radius of $R$.
--
--   Together with the matrix-geometric property $\pi_{n+1} = \pi_n R$ of Chapter 6, this identifies stability with the convergence of $\sum_n R^n$.
--
--   **Formalization Note** Finitely many phases is `[Fintype ι]`. $R$ is defined probabilistically, with entries in $[0,\infty]$; the right-hand side states that every entry of $R$ is finite (which $\operatorname{sp}(R)$ presupposes, and which holds for an irreducible QBD) and that the spectral radius of the resulting real matrix, viewed as a complex matrix, is less than $1$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 151, Corollary 7.1.2

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD
import Definitions.Def_MatrixAnalytic_Stability_Passage

open scoped ENNReal

namespace MatrixAnalytic.Stability

/-- Corollary 7.1.2 (p. 151). If the number of phases is finite, an irreducible QBD is positive
recurrent iff `sp(R) < 1`, where `R_{ij}` is the expected number of visits to `(1, j)` from
`(0, i)` before the first return to `ℓ(0)`. The right-hand side also records that the entries of
`R` are finite, which `sp(R)` presupposes; the spectral radius is taken over `ℂ`. -/
theorem positive_recurrent_iff_sp_lt_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂) ↔
      (∀ i j : ι, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
        spectralRadius ℂ
          (Matrix.of fun i j : ι => (((matR (qbdP B A₀ A₁ A₂) i j).toReal : ℝ) : ℂ)) < 1 := by sorry

end MatrixAnalytic.Stability
