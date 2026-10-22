-- Prove2me | Theorems.Thm_MatrixAnalytic_MatrixGeometric_UGR_quadratic
-- name    : MatrixAnalytic.MatrixGeometric.UGR_quadratic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:06.277894+00:00
-- url     : https://prove2.me/theorems/9a13250e-5872-405c-bce7-e59921597062
-- title:
--   Theorem 6.2.10 — U = A₁ + A₀(I−U)⁻¹A₂, G = A₂ + A₁G + A₀G², R = A₀ + RA₁ + R²A₂
-- statement:
--   Consider an irreducible, positive recurrent homogeneous QBD with blocks $B,A_0,A_1,A_2$. Fix a level $n\ge1$ and let $U$, $G$ (Eqs. (6.5), (6.6)) and $R$ (expected visits to $\ell(n+1)$ from $\ell(n)$ before a return to $\ell(0)\cup\cdots\cup\ell(n)$) be the matrices at level $n$, with $(I-U)^{-1}=\sum_{\nu\ge0}U^\nu$. Then
--   $$U=A_1+A_0(I-U)^{-1}A_2,\qquad G=A_2+A_1G+A_0G^2,\qquad R=A_0+RA_1+R^2A_2.$$
--
--   These three nonlinear matrix equations are the starting point of every algorithm that computes $R$ or $G$ (Chapter 8).
--
--   **Formalization Note** $U$, $G$, $R$ are defined probabilistically (taboo first-passage probabilities and expected numbers of visits), never as solutions of these equations. Entries lie in $[0,+\infty]$ and products and series are computed there. Aperiodicity, a temporary standing assumption of §6.2, is not used and is omitted.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 138, Theorem 6.2.10, Eqs. (6.13)–(6.15)

import Mathlib
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Chain
import Definitions.Def_MatrixAnalytic_MatrixGeometric_QBD
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Passage

open scoped ENNReal

namespace MatrixAnalytic.MatrixGeometric

/-- Theorem 6.2.10 (p. 138). For every level `n ≥ 1`, with `U` (6.5), `G` (6.6) at level `n`,
`R` the expected-visits matrix of Theorem 6.2.1 at level `n`, and `(I − U)⁻¹ := Σ_{ν≥0} Uᵛ`:
`U = A₁ + A₀(I − U)⁻¹A₂` (6.13), `G = A₂ + A₁G + A₀G²` (6.14), `R = A₀ + RA₁ + R²A₂` (6.15).
Products and series are computed in `ℝ≥0∞`. -/
theorem UGR_quadratic {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) (n : ℕ) (hn : 1 ≤ n) :
    matU (qbdP B A₀ A₁ A₂) n =
        ennMat A₁ + matMulE (matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂) n)))
          (ennMat A₂) ∧
      matG (qbdP B A₀ A₁ A₂) n =
        ennMat A₂ + matMulE (ennMat A₁) (matG (qbdP B A₀ A₁ A₂) n) +
          matMulE (ennMat A₀)
            (matMulE (matG (qbdP B A₀ A₁ A₂) n) (matG (qbdP B A₀ A₁ A₂) n)) ∧
      matR (qbdP B A₀ A₁ A₂) n =
        ennMat A₀ + matMulE (matR (qbdP B A₀ A₁ A₂) n) (ennMat A₁) +
          matMulE (matMulE (matR (qbdP B A₀ A₁ A₂) n) (matR (qbdP B A₀ A₁ A₂) n))
            (ennMat A₂) := by sorry

end MatrixAnalytic.MatrixGeometric
