-- Prove2me | Theorems.Thm_MatrixAnalytic_FirstPassage_passage_decomposition
-- name    : MatrixAnalytic.FirstPassage.passage_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:31.589908+00:00
-- url     : https://prove2.me/theorems/18777f95-faf7-4266-8d33-950ffc951f15
-- title:
--   Lemma 11.2.1 — t_{n→k} = t_{n→n+1} + Γ_{n→n+1}t_{n+1→k} and Γ_{n→k} = Γ_{n→n+1}Γ_{n+1→k}
-- statement:
--   Let $X$ be an irreducible finite QBD with levels $\ell(0),\dots,\ell(M)$, $M\ge1$, finitely many phases and transition matrix (10.2). For levels $n<k$ let $t_{n\to k}$ be the vector of expected first passage times from the states of $\ell(n)$ to $\ell(k)$ and $\Gamma_{n\to k}$ the matrix of first passage probabilities from $\ell(n)$ to $\ell(k)$ (initial phase, arrival phase), with the conventions $t_{n\to n}=0$ and $\Gamma_{n\to n}=I$. Then, for all $0\le n<k\le M$,
--   $$t_{n\to k}=t_{n\to n+1}+\Gamma_{n\to n+1}t_{n+1\to k},\qquad \Gamma_{n\to k}=\Gamma_{n\to n+1}\Gamma_{n+1\to k}.$$
--
--   Iterating, the first passage times and probabilities between any two levels are determined by those between consecutive levels (Eqs. (11.4)–(11.5)).
--
--   **Formalization Note** Expected times and probabilities are taboo path sums in `ℝ≥0∞`, and the identities are stated there, with matrix–vector products over the finite phase set.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 242, Lemma 11.2.1, Eqs. (11.2)–(11.3)

import Mathlib
import Definitions.Def_MatrixAnalytic_FirstPassage_Chain
import Definitions.Def_MatrixAnalytic_FirstPassage_QBD
import Definitions.Def_MatrixAnalytic_FirstPassage_Passage

open scoped ENNReal
open Matrix

namespace MatrixAnalytic.FirstPassage

/-- Lemma 11.2.1 (p. 242). For the finite QBD (10.2) and `0 ≤ n < k ≤ M`:
`t_{n→k} = t_{n→n+1} + Γ_{n→n+1} t_{n+1→k}` (11.2) and `Γ_{n→k} = Γ_{n→n+1} Γ_{n+1→k}` (11.3),
with the conventions `t_{n→n} = 0`, `Γ_{n→n} = I`. Expected times and probabilities are taboo
path sums in `ℝ≥0∞`. -/
theorem passage_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ)
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n k : ℕ) (hnk : n < k) (hkM : k ≤ M) :
    tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n k =
        tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1) +
          GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1) *ᵥ
            tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + 1) k ∧
      GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n k =
        GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1) *
          GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n + 1) k := by sorry

end MatrixAnalytic.FirstPassage
