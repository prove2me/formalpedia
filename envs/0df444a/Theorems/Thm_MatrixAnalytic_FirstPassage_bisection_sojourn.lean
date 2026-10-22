-- Prove2me | Theorems.Thm_MatrixAnalytic_FirstPassage_bisection_sojourn
-- name    : MatrixAnalytic.FirstPassage.bisection_sojourn
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:36.216954+00:00
-- url     : https://prove2.me/theorems/39c401ca-d67f-46cf-95e1-e034ae2525e0
-- title:
--   Lemma 11.3.3 — the doubling relations for the expected sojourn times s_i^{(n)}
-- statement:
--   Let $X$ be an irreducible finite QBD with levels $\ell(0),\dots,\ell(M)$, finitely many phases and transition matrix (10.2). For $1\le i\le n\le M-1$ let $\theta^{(n)}=\min(\tau(0),\tau(n+1))$, let $s_i^{(n)}$ be the vector of expected values of $\theta^{(n)}$ starting from the states of $\ell(i)$ (the expected sojourn time in $\ell(1)\cup\dots\cup\ell(n)$), and let $G_i^{(n)}$, $\Gamma_i^{(n)}$ be the probability matrices that this first exit is to $\ell(0)$, resp. $\ell(n+1)$. Let $n,\nu\ge1$ with $n+\nu\le M-1$. Then for $1\le i\le n$ and $1\le j\le\nu$
--   $$s_i^{(n+\nu)}=s_i^{(n)}+\Gamma_i^{(n)}s_1^{(\nu)}+\Gamma_i^{(n)}G_1^{(\nu)}s_n^{(n+\nu)},\qquad s_{n+j}^{(n+\nu)}=s_j^{(\nu)}+G_j^{(\nu)}s_n^{(n+\nu)},$$
--   and $s_n^{(n+\nu)}$, $s_n^{(n)}$, $s_1^{(\nu)}$ are finite, $I-\Gamma_n^{(n)}G_1^{(\nu)}$ is nonsingular, and
--   $$s_n^{(n+\nu)}=(I-\Gamma_n^{(n)}G_1^{(\nu)})^{-1}\{s_n^{(n)}+\Gamma_n^{(n)}s_1^{(\nu)}\}.$$
--
--   With Lemma 11.3.2 this gives $s_1^{(M-1)}$ and $G_1^{(M-1)}$ in $O(\log M)$ doubling steps.
--
--   **Formalization Note** The first and third relations are stated between `ℝ≥0∞`-valued vectors and matrices; the second between real readings, with the finiteness of the three vectors involved and the nonsingularity part of the conclusion. All quantities are defined for the chain $X$ itself, under the book's restriction $n+\nu\le M-1$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 247–248, Lemma 11.3.3

import Mathlib
import Definitions.Def_MatrixAnalytic_FirstPassage_Chain
import Definitions.Def_MatrixAnalytic_FirstPassage_QBD
import Definitions.Def_MatrixAnalytic_FirstPassage_Passage

open scoped ENNReal
open Matrix

namespace MatrixAnalytic.FirstPassage

/-- Lemma 11.3.3 (pp. 247–248). For the finite QBD (10.2) and `n, ν ≥ 1` with `n + ν ≤ M − 1`,
for `1 ≤ i ≤ n` and `1 ≤ j ≤ ν` (in `ℝ≥0∞`):
`s_i^{(n+ν)} = s_i^{(n)} + Γ_i^{(n)}s₁^{(ν)} + Γ_i^{(n)}G₁^{(ν)}s_n^{(n+ν)}` and
`s_{n+j}^{(n+ν)} = s_j^{(ν)} + G_j^{(ν)}s_n^{(n+ν)}`; moreover `s_n^{(n+ν)}`, `s_n^{(n)}`,
`s₁^{(ν)}` are finite, `I − Γ_n^{(n)}G₁^{(ν)}` is nonsingular and
`s_n^{(n+ν)} = (I − Γ_n^{(n)}G₁^{(ν)})⁻¹{s_n^{(n)} + Γ_n^{(n)}s₁^{(ν)}}`. -/
theorem bisection_sojourn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ)
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n ν : ℕ) (hn : 1 ≤ n) (hν : 1 ≤ ν)
    (hnν : n + ν < M) :
    (∀ i : ℕ, 1 ≤ i → i ≤ n →
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) i =
          sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i +
            GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i *ᵥ
              sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1 +
            (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n i *
              GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1) *ᵥ
                sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) ∧
      (∀ p : ι, sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n p ≠ ⊤ ∧
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n p ≠ ⊤ ∧
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1 p ≠ ⊤) ∧
      IsUnit (1 - toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) *
        toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1)) ∧
      toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) =
        (1 - toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) *
            toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1))⁻¹ *ᵥ
          (toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) +
            toRealMat (GamBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n n) *ᵥ
              toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν 1)) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ ν →
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) (n + j) =
          sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j +
            GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) ν j *ᵥ
              sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + ν) n) := by sorry

end MatrixAnalytic.FirstPassage
