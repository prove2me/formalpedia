-- Prove2me | Theorems.Thm_MatrixAnalytic_FirstPassage_bisection_doubling
-- name    : MatrixAnalytic.FirstPassage.bisection_doubling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:36.375978+00:00
-- url     : https://prove2.me/theorems/8c11ce10-19ad-49b7-96cb-a6433b61ff03
-- title:
--   Lemma 11.3.2 — the doubling relations (11.13)–(11.18) for G_i^{(n)} and Γ_i^{(n)}
-- statement:
--   Let $X$ be an irreducible finite QBD with levels $\ell(0),\dots,\ell(M)$, finitely many phases and transition matrix (10.2). For $1\le i\le n\le M-1$ let $\theta^{(n)}=\min(\tau(0),\tau(n+1))$ be the first passage time to $\ell(0)\cup\ell(n+1)$, and let $G_i^{(n)}$ (resp. $\Gamma_i^{(n)}$) be the matrix of probabilities, starting from $\ell(i)$, that this first passage is to $\ell(0)$ (resp. to $\ell(n+1)$), indexed by initial and arrival phase. Let $n,\nu\ge1$ with $n+\nu\le M-1$. Then for $1\le i\le n$ and $1\le j\le\nu$
--   $$G_i^{(n+\nu)}=G_i^{(n)}+\Gamma_i^{(n)}G_1^{(\nu)}G_n^{(n+\nu)},\qquad G_{n+j}^{(n+\nu)}=G_j^{(\nu)}G_n^{(n+\nu)},$$
--   $$\Gamma_i^{(n+\nu)}=\Gamma_i^{(n)}\Gamma_{n+1}^{(n+\nu)},\qquad \Gamma_{n+j}^{(n+\nu)}=\Gamma_j^{(\nu)}+G_j^{(\nu)}\Gamma_n^{(n)}\Gamma_{n+1}^{(n+\nu)}.$$
--   Moreover the matrices $I-\Gamma_n^{(n)}G_1^{(\nu)}$ and $I-G_1^{(\nu)}\Gamma_n^{(n)}$ are nonsingular and
--   $$G_n^{(n+\nu)}=(I-\Gamma_n^{(n)}G_1^{(\nu)})^{-1}G_n^{(n)},\qquad \Gamma_{n+1}^{(n+\nu)}=(I-G_1^{(\nu)}\Gamma_n^{(n)})^{-1}\Gamma_1^{(\nu)}.$$
--
--   These relations let one pass from the quantities for $n$ and $\nu$ levels to those for $n+\nu$ levels, the step of the Reduction by Bisection algorithm (Figure 11.2).
--
--   **Formalization Note** The four relations (11.13)–(11.16) are stated between the `ℝ≥0∞`-valued probability matrices; (11.17)–(11.18) are stated between their real readings, with nonsingularity part of the conclusion. All quantities are defined for the chain $X$ itself; the restriction $n+\nu\le M-1$ is the book's (the matrix $P_\omega^{(n)}$ of (11.11) describes any $n$ contiguous levels $\ell(k+1),\dots,\ell(k+n)$ with $0\le k\le M-1-n$), and the identification of $G_j^{(\nu)}$ with the corresponding quantity on the shifted levels $\ell(n+1),\dots,\ell(n+\nu)$ is part of what is to be proved.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 246–247, Lemma 11.3.2, Eqs. (11.13)–(11.18)

import Mathlib
import Definitions.Def_MatrixAnalytic_FirstPassage_Chain
import Definitions.Def_MatrixAnalytic_FirstPassage_QBD
import Definitions.Def_MatrixAnalytic_FirstPassage_Passage

open scoped ENNReal
open Matrix

namespace MatrixAnalytic.FirstPassage

/-- Lemma 11.3.2 (pp. 246–247). For the finite QBD (10.2) and `n, ν ≥ 1` with `n + ν ≤ M − 1`
(so that the levels `1, …, n + ν` all move with the matrix `P_ω^{(n+ν)}` of (11.11)):
(11.13)–(11.16) for `1 ≤ i ≤ n`, `1 ≤ j ≤ ν` (in `ℝ≥0∞`), and the matrices
`I − Γ_n^{(n)}G₁^{(ν)}`, `I − G₁^{(ν)}Γ_n^{(n)}` are nonsingular with
`G_n^{(n+ν)} = (I − Γ_n^{(n)}G₁^{(ν)})⁻¹G_n^{(n)}` (11.17) and
`Γ_{n+1}^{(n+ν)} = (I − G₁^{(ν)}Γ_n^{(n)})⁻¹Γ₁^{(ν)}` (11.18). -/
theorem bisection_doubling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ)
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n ν : ℕ) (hn : 1 ≤ n) (hν : 1 ≤ ν)
    (hnν : n + ν < M) :
    (∀ i : ℕ, 1 ≤ i → i ≤ n →
        GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) i =
          GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i +
            GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i *
              GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1 *
                GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ ν →
        GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + j) =
          GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j *
            GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ n →
        GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) i =
          GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i *
            GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + 1)) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ ν →
        GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + j) =
          GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j +
            GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j *
              GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n *
                GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + 1)) ∧
      IsUnit (1 - toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) *
        toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1)) ∧
      toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) =
        (1 - toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) *
            toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1))⁻¹ *
          toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) ∧
      IsUnit (1 - toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1) *
        toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n)) ∧
      toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + 1)) =
        (1 - toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1) *
            toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n))⁻¹ *
          toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1) := by sorry

end MatrixAnalytic.FirstPassage
