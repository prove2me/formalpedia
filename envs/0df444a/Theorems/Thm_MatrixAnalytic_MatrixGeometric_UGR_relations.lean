-- Prove2me | Theorems.Thm_MatrixAnalytic_MatrixGeometric_UGR_relations
-- name    : MatrixAnalytic.MatrixGeometric.UGR_relations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:02.742503+00:00
-- url     : https://prove2.me/theorems/eb0e45c7-7d62-4904-8b9d-6248f3c03cb7
-- title:
--   Theorem 6.2.9 — R = A₀(I−U)⁻¹, G = (I−U)⁻¹A₂, U = A₁ + A₀G = A₁ + RA₂
-- statement:
--   Consider an irreducible, positive recurrent homogeneous QBD with blocks $B,A_0,A_1,A_2$. Fix a level $n\ge1$. Let $U$ and $G$ be the matrices (6.5) and (6.6) at level $n$: $U_{ij}$ is the probability, starting from $(n,i)$, of returning to $\ell(n)$ before visiting $\ell(n-1)$ and doing so at $(n,j)$, and $G_{ij}$ is the probability, starting from $(n,i)$, of visiting $\ell(n-1)$ in a finite time and doing so first at $(n-1,j)$. Let $R_{ij}$ be the expected number of visits to $(n+1,j)$, starting from $(n,i)$, before a return to $\ell(0)\cup\cdots\cup\ell(n)$, and let $(I-U)^{-1}=\sum_{\nu\ge0}U^\nu$. Then
--   $$R=A_0(I-U)^{-1},\qquad G=(I-U)^{-1}A_2,\qquad U=A_1+A_0G,\qquad U=A_1+RA_2.$$
--
--   So any one of $U$, $G$, $R$ determines the other two.
--
--   **Formalization Note** All matrices have entries in $[0,+\infty]$, products and the series $\sum_\nu U^\nu$ are computed there, and $(I-U)^{-1}$ denotes that series, as in the book (p. 109); no invertibility is asserted or assumed. The equations are stated for the matrices at an arbitrary level $n\ge1$. Aperiodicity, a temporary standing assumption of §6.2, is not used and is omitted.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 137, Theorem 6.2.9, Eqs. (6.9)–(6.12)

import Mathlib
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Chain
import Definitions.Def_MatrixAnalytic_MatrixGeometric_QBD
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Passage

open scoped ENNReal

namespace MatrixAnalytic.MatrixGeometric

/-- Theorem 6.2.9 (p. 137). For every level `n ≥ 1`, with `U` (6.5), `G` (6.6) at level `n` and
`R` the expected-visits matrix of Theorem 6.2.1 at level `n`, and `(I − U)⁻¹ := Σ_{ν≥0} Uᵛ`:
`R = A₀(I − U)⁻¹` (6.9), `G = (I − U)⁻¹A₂` (6.10), `U = A₁ + A₀G` (6.11), `U = A₁ + RA₂` (6.12).
Products and series are computed in `ℝ≥0∞`. -/
theorem UGR_relations {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) (n : ℕ) (hn : 1 ≤ n) :
    matR (qbdP B A₀ A₁ A₂) n =
        matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂) n)) ∧
      matG (qbdP B A₀ A₁ A₂) n =
        matMulE (seriesInvE (matU (qbdP B A₀ A₁ A₂) n)) (ennMat A₂) ∧
      matU (qbdP B A₀ A₁ A₂) n = ennMat A₁ + matMulE (ennMat A₀) (matG (qbdP B A₀ A₁ A₂) n) ∧
      matU (qbdP B A₀ A₁ A₂) n = ennMat A₁ + matMulE (matR (qbdP B A₀ A₁ A₂) n) (ennMat A₂) := by sorry

end MatrixAnalytic.MatrixGeometric
