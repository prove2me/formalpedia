-- Prove2me | Theorems.Thm_MatrixAnalytic_Nonhomogeneous_minimal_solutions
-- name    : MatrixAnalytic.Nonhomogeneous.minimal_solutions
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:46.582912+00:00
-- url     : https://prove2.me/theorems/ef406650-4880-460e-aec0-7d2b6471a46a
-- title:
--   Theorem 12.1.3 — G⁽ⁿ⁾, R⁽ⁿ⁾, U⁽ⁿ⁾ satisfy (12.7)–(12.9) and are their minimal nonnegative solutions
-- statement:
--   Let $P$ be the transition matrix (12.1) of a nonhomogeneous QBD that is stochastic and irreducible, every level having a nonempty countable set of phases, with first-passage matrices $G^{(n)}$, taboo first-return matrices $U^{(n)}$ and expected-visits matrices $R^{(n)}$, $n\ge1$. Write $(I-M)^{-1}=\sum_{\nu\ge0}M^\nu$. Then for every $n\ge1$
--   $$G^{(n)} = A_2^{(n)} + A_1^{(n)}G^{(n)} + A_0^{(n)}G^{(n+1)}G^{(n)}, \tag{12.7}$$
--   $$R^{(n)} = A_0^{(n-1)} + R^{(n)}A_1^{(n)} + R^{(n)}R^{(n+1)}A_2^{(n+1)}, \tag{12.8}$$
--   $$U^{(n)} = A_1^{(n)} + A_0^{(n)}(I - U^{(n+1)})^{-1}A_2^{(n+1)}, \tag{12.9}$$
--   all entries of $G^{(n)}$, $R^{(n)}$, $U^{(n)}$ being finite, and each sequence is the minimal nonnegative solution of its system:
--
--   1. if $\{X^{(n)}: n\ge1\}$ is any sequence of nonnegative real matrices (of the dimensions of $G^{(n)}$) satisfying (12.7) for all $n\ge1$, then $G^{(n)}\le X^{(n)}$ entrywise for all $n\ge1$;
--   2. if $\{Z^{(n)}: n\ge1\}$ is any sequence of nonnegative real matrices satisfying (12.8) for all $n\ge1$, then $R^{(n)}\le Z^{(n)}$ entrywise for all $n\ge1$;
--   3. if $\{X^{(n)}: n\ge1\}$ is any sequence of nonnegative real square matrices satisfying (12.9) for all $n\ge1$, then $U^{(n)}\le X^{(n)}$ entrywise for all $n\ge1$.
--
--   Minimality is among whole sequences solving the infinite system for all levels simultaneously, not level by level. The theorem characterizes the probabilistically defined matrices as the least solutions of nonlinear matrix equations that couple consecutive levels, which is what justifies computing them by monotone iteration.
--
--   **Formalization Note** $G^{(m+1)}$, $R^{(m+1)}$ are `matG P m`, `matR P m` and a competitor sequence for (12.7) or (12.8) is indexed the same way (its $m$-th term is the term of level $m+1$); $U^{(n)}$ is `matU P n` and a competitor for (12.9) is indexed by the level, its level-$0$ term being unconstrained. $A_2^{(m+1)}$ is `A₂ m`. Products and the series $(I-M)^{-1}$ are evaluated entrywise in $[0,\infty]$, so they are always defined; for a competitor in (12.9) the series need not converge. The matrices $G^{(n)}$, $U^{(n)}$, $R^{(n)}$ are defined as first-passage probabilities and expected numbers of visits (sums over taboo trajectories), never as solutions of these equations.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 261, Theorem 12.1.3 (minimality as in footnote 13, p. 171)

import Mathlib
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Chain
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_QBD
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Passage

open scoped ENNReal

namespace MatrixAnalytic.Nonhomogeneous

/-- Theorem 12.1.3 (p. 261). For an irreducible nonhomogeneous QBD (12.1), with
`G^{(m+1)} = matG P m`, `R^{(m+1)} = matR P m`, `U^{(n)} = matU P n` and
`(I − U)⁻¹ := Σ_ν U^ν`, for every level `n ≥ 1`:
1. `{G^{(n)}}` solves (12.7) `G^{(n)} = A₂^{(n)} + A₁^{(n)} G^{(n)} + A₀^{(n)} G^{(n+1)} G^{(n)}`
   and lies entrywise below every sequence `{X^{(n)} : n ≥ 1}` of nonnegative real matrices
   solving (12.7) for all `n ≥ 1`;
2. `{R^{(n)}}` solves (12.8) `R^{(n)} = A₀^{(n−1)} + R^{(n)} A₁^{(n)} + R^{(n)} R^{(n+1)} A₂^{(n+1)}`
   and lies entrywise below every nonnegative real solution sequence `{Z^{(n)} : n ≥ 1}`;
3. `{U^{(n)}}` solves (12.9) `U^{(n)} = A₁^{(n)} + A₀^{(n)} (I − U^{(n+1)})⁻¹ A₂^{(n+1)}`
   and lies entrywise below every nonnegative real solution sequence `{X^{(n)} : n ≥ 1}`.
The entries of `G^{(n)}`, `R^{(n)}`, `U^{(n)}` are finite. A competitor sequence for (12.7) or
(12.8) is indexed like `G`, `R` (its `m`-th term is the term of level `m + 1`); one for (12.9)
is indexed by the level, its term at level `0` being unconstrained. Products and series are
computed in `ℝ≥0∞`. -/
theorem minimal_solutions {ι : ℕ → Type*} [∀ n, Countable (ι n)]
    [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ) (P : (Σ n, ι n) → (Σ n, ι n) → ℝ)
    (hPdef : P = ndqbdP A₀ A₁ A₂)
    (hP : IsStochasticC P) (hirr : IrreducibleC P) :
    -- (12.7): `{G^{(n)}}` is a solution and the minimal nonnegative one
    ((∀ m : ℕ, ∀ i j, matG P m i j ≠ ⊤) ∧
      (∀ m : ℕ, matG P m = ennMat (A₂ m) + matMulE (ennMat (A₁ (m + 1))) (matG P m) +
        matMulE (ennMat (A₀ (m + 1))) (matMulE (matG P (m + 1)) (matG P m))) ∧
      ∀ X : (m : ℕ) → ι (m + 1) → ι m → ℝ, (∀ m i j, 0 ≤ X m i j) →
        (∀ m : ℕ, ennMat (X m) = ennMat (A₂ m) + matMulE (ennMat (A₁ (m + 1))) (ennMat (X m)) +
          matMulE (ennMat (A₀ (m + 1))) (matMulE (ennMat (X (m + 1))) (ennMat (X m)))) →
        ∀ m i j, matG P m i j ≤ ennMat (X m) i j) ∧
    -- (12.8): `{R^{(n)}}` is a solution and the minimal nonnegative one
    ((∀ m : ℕ, ∀ i j, matR P m i j ≠ ⊤) ∧
      (∀ m : ℕ, matR P m = ennMat (A₀ m) + matMulE (matR P m) (ennMat (A₁ (m + 1))) +
        matMulE (matMulE (matR P m) (matR P (m + 1))) (ennMat (A₂ (m + 1)))) ∧
      ∀ Z : (m : ℕ) → ι m → ι (m + 1) → ℝ, (∀ m i j, 0 ≤ Z m i j) →
        (∀ m : ℕ, ennMat (Z m) = ennMat (A₀ m) + matMulE (ennMat (Z m)) (ennMat (A₁ (m + 1))) +
          matMulE (matMulE (ennMat (Z m)) (ennMat (Z (m + 1)))) (ennMat (A₂ (m + 1)))) →
        ∀ m i j, matR P m i j ≤ ennMat (Z m) i j) ∧
    -- (12.9): `{U^{(n)}}` is a solution and the minimal nonnegative one
    ((∀ n : ℕ, 1 ≤ n → ∀ i j, matU P n i j ≠ ⊤) ∧
      (∀ n : ℕ, 1 ≤ n → matU P n = ennMat (A₁ n) +
        matMulE (matMulE (ennMat (A₀ n)) (seriesInvE (matU P (n + 1)))) (ennMat (A₂ n))) ∧
      ∀ X : (n : ℕ) → ι n → ι n → ℝ, (∀ n : ℕ, 1 ≤ n → ∀ i j, 0 ≤ X n i j) →
        (∀ n : ℕ, 1 ≤ n → ennMat (X n) = ennMat (A₁ n) +
          matMulE (matMulE (ennMat (A₀ n)) (seriesInvE (ennMat (X (n + 1))))) (ennMat (A₂ n))) →
        ∀ n : ℕ, 1 ≤ n → ∀ i j, matU P n i j ≤ ennMat (X n) i j) := by sorry

end MatrixAnalytic.Nonhomogeneous
