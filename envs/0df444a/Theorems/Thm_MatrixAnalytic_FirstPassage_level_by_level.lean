-- Prove2me | Theorems.Thm_MatrixAnalytic_FirstPassage_level_by_level
-- name    : MatrixAnalytic.FirstPassage.level_by_level
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:39.581522+00:00
-- url     : https://prove2.me/theorems/a4c5436f-d9b8-4967-a1cd-272e993b6070
-- title:
--   Lemma 11.2.2 — Γ_{n→n+1} = (I − C_n)⁻¹A₀, t_{0→1} = (I − C₀)⁻¹1, t_{n→n+1} = (I − C_n)⁻¹1 + (I − C_n)⁻¹A₂t_{n−1→n}
-- statement:
--   Let $X$ be an irreducible finite QBD with levels $\ell(0),\dots,\ell(M)$, $M\ge1$, finitely many phases and transition matrix (10.2) with blocks $P_{00},A_0,A_1,A_2,P_{MM}$. Let $t_{n\to n+1}$ and $\Gamma_{n\to n+1}$ be the expected first passage times and the first passage probabilities from $\ell(n)$ to $\ell(n+1)$, and define
--   $$C_0=P_{00},\qquad C_n=A_1+A_2\Gamma_{n-1\to n}\quad(1\le n\le M-1).$$
--   Then for $0\le n\le M-1$ the matrix $I-C_n$ is nonsingular and
--   $$\Gamma_{n\to n+1}=(I-C_n)^{-1}A_0;$$
--   the expected first passage times $t_{n\to n+1}$ are finite, and
--   $$t_{0\to1}=(I-C_0)^{-1}\mathbf 1,\qquad t_{n\to n+1}=(I-C_n)^{-1}\mathbf 1+(I-C_n)^{-1}A_2t_{n-1\to n}\quad(1\le n\le M-1).$$
--
--   Together with Lemma 11.2.1 this computes $t_{0\to M}$ level by level (the Linear Level Reduction Algorithm, Figure 11.1).
--
--   **Formalization Note** The book prints $C_n=A_1+A_2(I-C_{n-1}^{-1})A_0=A_1+A_2\Gamma_{n-1\to n}$. The two printed expressions differ (finding F1: the inverse is misplaced in the first), and the statement formalizes the second, $A_1+A_2\Gamma_{n-1\to n}$, which is what the proof uses; a corrected variant states the recursion $C_n=A_1+A_2(I-C_{n-1})^{-1}A_0$ of (10.3). Nonsingularity of $I-C_n$ is part of the conclusion (the book proves it, via Lemma 10.1.1), and $\Gamma_{n\to n+1}$, $t_{n\to n+1}$ are read as real matrices and vectors, their finiteness being asserted.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 242–243, Lemma 11.2.2, Eqs. (11.6)–(11.8)

import Mathlib
import Definitions.Def_MatrixAnalytic_FirstPassage_Chain
import Definitions.Def_MatrixAnalytic_FirstPassage_QBD
import Definitions.Def_MatrixAnalytic_FirstPassage_Passage

open scoped ENNReal
open Matrix

namespace MatrixAnalytic.FirstPassage

/-- Lemma 11.2.2 (pp. 242–243). For the finite QBD (10.2), with `C₀ = P₀₀` and
`C_n = A₁ + A₂Γ_{n−1→n}` (`matC`): for `0 ≤ n ≤ M − 1` the matrix `I − C_n` is nonsingular and
`Γ_{n→n+1} = (I − C_n)⁻¹A₀` (11.6); the expected first passage times `t_{n→n+1}` are finite,
`t_{0→1} = (I − C₀)⁻¹1` (11.7) and, for `1 ≤ n ≤ M − 1`,
`t_{n→n+1} = (I − C_n)⁻¹1 + (I − C_n)⁻¹A₂t_{n−1→n}` (11.8). -/
theorem level_by_level {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℕ) (P₀₀ A₀ A₁ A₂ P_MM : Matrix ι ι ℝ)
    (hQ : IsFiniteQBD M P₀₀ A₀ A₁ A₂ P_MM) :
    (∀ n : ℕ, n < M →
        IsUnit (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n) ∧
        toRealMat (GammaPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) =
          (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n)⁻¹ * A₀) ∧
      (∀ n : ℕ, n < M → ∀ i : ι, tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1) i ≠ ⊤) ∧
      toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) 0 1) =
        (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ 0)⁻¹ *ᵥ (fun _ => (1 : ℝ)) ∧
      (∀ n : ℕ, 1 ≤ n → n < M →
        toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) n (n + 1)) =
          (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n)⁻¹ *ᵥ (fun _ => (1 : ℝ)) +
          (1 - matC (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) P₀₀ A₁ A₂ n)⁻¹ *ᵥ
            (A₂ *ᵥ toRealVec (tPass (finiteQBD M P₀₀ A₀ A₁ A₂ P_MM) (n - 1) n))) := by sorry

end MatrixAnalytic.FirstPassage
