-- Prove2me | Theorems.Thm_MatrixAnalytic_MinimalSolutions_Fk_recurrence
-- name    : MatrixAnalytic.MinimalSolutions.Fk_recurrence
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:36.563759+00:00
-- url     : https://prove2.me/theorems/630034c1-1bae-486b-8e1e-31f4f7577a2e
-- title:
--   Lemma 8.2.1 — F(k) recurrences, F(k) ↑ Ĝ, Ĝ (sub)stochastic, minimal solution of (8.28), sp(Ĝ) > 0
-- statement:
--   Let $X$ be an irreducible homogeneous QBD with transition matrix (8.1) and a finite, nonempty set of phases. For $k\ge1$ let $F(k)$ be the first-passage matrix from $\ell(k)$ to $\ell(k+1)$ under taboo of $\ell(0)$,
--
--   $$F(k) = \mathrm P[\gamma(0)>\gamma(k+1)\ \&\ X_{\gamma(k+1)}\mid X_0\in\ell(k)],$$
--
--   and let $\hat G$ be the matrix of first passage probabilities from $\ell(1)$ to $\ell(0)$ for the level-reversed QBD (8.25), in which the roles of $A_0$ and $A_2$ are exchanged (its boundary block $\hat B_1$ is arbitrary). Then:
--
--   1. $F(1) = (I-A_1)^{-1}A_0$ (8.26) and $F(k+1) = [I - A_1 - A_2F(k)]^{-1}A_0$ for $k\ge1$ (8.27), the inverses existing;
--   2. the sequence $\{F(k)\}$ is monotone increasing and converges to $\hat G$;
--   3. if the original QBD is positive recurrent, then $\hat G$ is substochastic; if it is null recurrent or transient, then $\hat G$ is stochastic;
--   4. $\hat G$ is the minimal nonnegative solution of
--   $$\hat G = A_0 + A_1\hat G + A_2\hat G^2; \tag{8.28}$$
--   5. the spectral radius of $\hat G$ is strictly positive.
--
--   The lemma is the tool for the convergence rate of the linear progression algorithm (Theorem 8.2.2), through the factorization $G - G(k) = \prod_{1\le i\le k}F(i)\,G^{k+1}$.
--
--   **Formalization Note** The phase set is finite and nonempty (the book's phases are $1\le i\le m$), finite because the spectral radius in item 5 is that of a finite matrix (Section 8.2 assumes $m$ finite at several places). $(I-M)^{-1}$ is the series $\sum_\nu M^\nu$ computed in $[0,\infty]$, and its convergence is part of the conclusion. "Substochastic" in item 3 is read as the opposite of stochastic, as the dichotomy requires: every row sum is at most $1$ and some row sum is strictly less than $1$. "Null recurrent or transient" is "not positive recurrent". The spectral radius is that of $\hat G$ as a complex matrix. Finding F1 of this mission records that the stochasticity claim of item 3 fails when $A = A_0+A_1+A_2$ is reducible; the statement is given here exactly as printed.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 177, Lemma 8.2.1 (F(k) as in Eq. (8.22), p. 176; level-reversed QBD Eq. (8.25), p. 176)

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage

open scoped ENNReal

namespace MatrixAnalytic.MinimalSolutions

/-- Lemma 8.2.1 (p. 177). For an irreducible QBD (8.1) with finitely many phases (at least one), let `F(k)`
(8.22) be the first-passage matrix from `ℓ(k)` to `ℓ(k + 1)` under taboo of `ℓ(0)`, and `Ĝ` the
first-passage matrix from `ℓ(1)` to `ℓ(0)` of the level-reversed QBD (8.25) (`A₀`, `A₂`
exchanged, any boundary block `B̂₁ = Bhat`). Then `F(1) = (I − A₁)⁻¹A₀` (8.26),
`F(k + 1) = [I − A₁ − A₂F(k)]⁻¹A₀` (8.27) with `(I − M)⁻¹ := Σ_ν M^ν` convergent; `F(k)` increases
to `Ĝ`; `Ĝ` is substochastic (row sums `≤ 1`, one `< 1`) if the QBD is positive recurrent and
stochastic otherwise; `Ĝ` is the minimal nonnegative solution of (8.28)
`Ĝ = A₀ + A₁Ĝ + A₂Ĝ²`; and `sp(Ĝ) > 0`. Products and series are computed in `ℝ≥0∞`. -/
theorem Fk_recurrence {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (Bhat : ι → ι → ℝ) :
    -- (8.26)
    ((∀ i j, seriesInvE (ennMat A₁) i j ≠ ⊤) ∧
      matF (qbdP B A₀ A₁ A₂) 1 = matMulE (seriesInvE (ennMat A₁)) (ennMat A₀)) ∧
    -- (8.27)
    (∀ k : ℕ, 1 ≤ k →
      (∀ i j, seriesInvE (ennMat A₁ + matMulE (ennMat A₂) (matF (qbdP B A₀ A₁ A₂) k)) i j ≠ ⊤) ∧
        matF (qbdP B A₀ A₁ A₂) (k + 1) =
          matMulE (seriesInvE (ennMat A₁ + matMulE (ennMat A₂) (matF (qbdP B A₀ A₁ A₂) k)))
            (ennMat A₀)) ∧
    -- monotone convergence to `Ĝ`
    (∀ k : ℕ, 1 ≤ k → ∀ i j, matF (qbdP B A₀ A₁ A₂) k i j ≤ matF (qbdP B A₀ A₁ A₂) (k + 1) i j) ∧
    (∀ i j, Filter.Tendsto (fun k => matF (qbdP B A₀ A₁ A₂) k i j) Filter.atTop
      (nhds (matG (qbdP Bhat A₂ A₁ A₀) i j))) ∧
    -- positive recurrent: `Ĝ` substochastic
    ((∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) →
      (∀ i, ∑' j, matG (qbdP Bhat A₂ A₁ A₀) i j ≤ 1) ∧ ∃ i, ∑' j, matG (qbdP Bhat A₂ A₁ A₀) i j < 1) ∧
    -- null recurrent or transient: `Ĝ` stochastic
    (¬ (∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) →
      ∀ i, ∑' j, matG (qbdP Bhat A₂ A₁ A₀) i j = 1) ∧
    -- (8.28): `Ĝ` is a nonnegative solution and is minimal
    ((∀ i j, matG (qbdP Bhat A₂ A₁ A₀) i j ≠ ⊤) ∧
      matG (qbdP Bhat A₂ A₁ A₀) = ennMat A₀ + matMulE (ennMat A₁) (matG (qbdP Bhat A₂ A₁ A₀)) +
        matMulE (ennMat A₂) (matMulE (matG (qbdP Bhat A₂ A₁ A₀)) (matG (qbdP Bhat A₂ A₁ A₀))) ∧
      ∀ Y : ι → ι → ℝ, (∀ i j, 0 ≤ Y i j) →
        ennMat Y = ennMat A₀ + matMulE (ennMat A₁) (ennMat Y) +
          matMulE (ennMat A₂) (matMulE (ennMat Y) (ennMat Y)) →
        ∀ i j, matG (qbdP Bhat A₂ A₁ A₀) i j ≤ ennMat Y i j) ∧
    -- the spectral radius of `Ĝ` is strictly positive
    0 < spectralRadius ℂ
      (Matrix.of fun i j => (((matG (qbdP Bhat A₂ A₁ A₀) i j).toReal : ℝ) : ℂ)) := by sorry

end MatrixAnalytic.MinimalSolutions
