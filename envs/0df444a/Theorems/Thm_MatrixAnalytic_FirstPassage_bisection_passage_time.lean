-- Prove2me | Theorems.Thm_MatrixAnalytic_FirstPassage_bisection_passage_time
-- name    : MatrixAnalytic.FirstPassage.bisection_passage_time
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:37.104251+00:00
-- url     : https://prove2.me/theorems/a76e5c11-fead-42e3-a425-0ea603c9ce18
-- title:
--   Lemma 11.3.1 — t_{0→M} = (I − Γ_{0→1}G₁^{(M−1)})⁻¹{t_{0→1} + Γ_{0→1}s₁^{(M−1)}}
-- statement:
--   Let $X$ be an irreducible finite QBD with levels $\ell(0),\dots,\ell(M)$, $M\ge2$, finitely many phases and transition matrix (10.2). Let $t_{0\to M}$ and $t_{0\to1}$ be the vectors of expected first passage times from the states of $\ell(0)$ to $\ell(M)$ and to $\ell(1)$, and $\Gamma_{0\to1}$ the matrix of first passage probabilities from $\ell(0)$ to $\ell(1)$. Let $\theta=\min(\tau(0),\tau(M))$ be the first passage time to $\ell(0)\cup\ell(M)$, $s_1^{(M-1)}$ the vector of its expected values starting from $\ell(1)$ (the expected sojourn time in $\ell(1)\cup\dots\cup\ell(M-1)$), and $G_1^{(M-1)}$ the matrix of probabilities, starting from $\ell(1)$, that this passage is to $\ell(0)$, indexed by initial and arrival phase. Then $t_{0\to M}$, $t_{0\to1}$ and $s_1^{(M-1)}$ are finite, the matrix $I-\Gamma_{0\to1}G_1^{(M-1)}$ is nonsingular, and
--   $$t_{0\to M}=(I-\Gamma_{0\to1}G_1^{(M-1)})^{-1}\{t_{0\to1}+\Gamma_{0\to1}s_1^{(M-1)}\}.$$
--
--   This reduces the expected first passage time across all $M$ levels to quantities for the homogeneous block of levels $1,\dots,M-1$, which Lemmas 11.3.2 and 11.3.3 compute by repeated doubling.
--
--   **Formalization Note** Expected times and probabilities are taboo path sums in `ℝ≥0∞` and are read as real vectors and matrices; their finiteness and the nonsingularity of $I-\Gamma_{0\to1}G_1^{(M-1)}$ are part of the conclusion (the book proves both from irreducibility), so the inverse is never Lean's junk value.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 245–246, Lemma 11.3.1, Eq. (11.12)

import Mathlib
import Definitions.Def_MatrixAnalytic_FirstPassage_Chain
import Definitions.Def_MatrixAnalytic_FirstPassage_QBD
import Definitions.Def_MatrixAnalytic_FirstPassage_Passage

open scoped ENNReal
open Matrix

namespace MatrixAnalytic.FirstPassage

/-- Lemma 11.3.1 (pp. 245–246). For the finite QBD (10.2) with `M ≥ 2`, the expected first
passage times from `ℓ(0)` to `ℓ(M)` satisfy
`t_{0→M} = (I − Γ_{0→1}G₁^{(M−1)})⁻¹{t_{0→1} + Γ_{0→1}s₁^{(M−1)}}` (11.12): the vectors
`t_{0→M}`, `t_{0→1}`, `s₁^{(M−1)}` are finite, `I − Γ_{0→1}G₁^{(M−1)}` is nonsingular, and the
identity holds between the real matrices and vectors. -/
theorem bisection_passage_time {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ)
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) (hM : 2 ≤ M) :
    (∀ i : ι, tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) 0 M i ≠ ⊤ ∧
        tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) 0 1 i ≠ ⊤ ∧
        sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (M - 1) 1 i ≠ ⊤) ∧
      IsUnit (1 - toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) 0 1) *
        toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (M - 1) 1)) ∧
      toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) 0 M) =
        (1 - toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) 0 1) *
            toRealMat (GBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (M - 1) 1))⁻¹ *ᵥ
          (toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) 0 1) +
            toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) 0 1) *ᵥ
              toRealVec (sBis (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (M - 1) 1)) := by sorry

end MatrixAnalytic.FirstPassage
