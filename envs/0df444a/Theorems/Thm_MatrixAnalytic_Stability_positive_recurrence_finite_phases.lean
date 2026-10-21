-- Prove2me | Theorems.Thm_MatrixAnalytic_Stability_positive_recurrence_finite_phases
-- name    : MatrixAnalytic.Stability.positive_recurrence_finite_phases
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:34.241023+00:00
-- url     : https://prove2.me/theorems/84009e78-afc8-4d07-b81c-ffc29eb322fc
-- title:
--   Theorem 7.1.1 (last paragraph) — with finitely many phases, a QBD is positive recurrent iff G is stochastic and G′(1) is finite
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and finitely many phases, and assume $P$ is stochastic and irreducible. Let $G$ be the first-passage matrix from $\ell(1)$ to $\ell(0)$, and let
--   $$(G'(1))_{ij} = \mathrm E[\delta_0\,\mathcal I\{X_{\delta_0} = (0, j)\} \mid X_0 = (1, i)] \tag{7.2}$$
--   with $\delta_0$ the first passage time to $\ell(0)$. Then the QBD is positive recurrent if and only if $G$ is stochastic ($G\mathbf 1 = \mathbf 1$) and every entry of $G'(1)$ is finite.
--
--   This is the form of Theorem 7.1.1 used for the drift criterion: positive recurrence becomes a statement about the first passage from one level to the one below.
--
--   **Formalization Note** Finitely many phases is `[Fintype ι]`. Positive recurrence of the QBD means that every state has a finite expected return time. $G'(1)$ takes values in $[0,\infty]$, and "finite" is $\ne \infty$ for every entry.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 149, Theorem 7.1.1 (last paragraph)

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD
import Definitions.Def_MatrixAnalytic_Stability_Passage

open scoped ENNReal

namespace MatrixAnalytic.Stability

/-- Theorem 7.1.1, last paragraph (p. 149). If the number of phases is finite, an irreducible
QBD is positive recurrent iff its first-passage matrix `G` (from `ℓ(1)` to `ℓ(0)`) is
stochastic and every entry of `G′(1)` (7.2) is finite. -/
theorem positive_recurrence_finite_phases {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂) ↔
      IsStochasticE (matG (qbdP B A₀ A₁ A₂) 0) ∧
        ∀ i j : ι, matGderiv (qbdP B A₀ A₁ A₂) 0 i j ≠ ⊤ := by sorry

end MatrixAnalytic.Stability
