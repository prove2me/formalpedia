-- Prove2me | Theorems.Thm_MatrixAnalytic_Nonhomogeneous_UGR_relations
-- name    : MatrixAnalytic.Nonhomogeneous.UGR_relations
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:59.350211+00:00
-- url     : https://prove2.me/theorems/41bd39e3-cb81-433c-adab-ac4172508ad0
-- title:
--   Theorem 12.1.2 — relations (12.3)–(12.6) between G⁽ⁿ⁾, U⁽ⁿ⁾ and R⁽ⁿ⁾
-- statement:
--   Let $P$ be the transition matrix (12.1) of a nonhomogeneous QBD that is stochastic and irreducible, every level having a nonempty countable set of phases. Let $G^{(n)}$, $U^{(n)}$, $R^{(n)}$ ($n\ge1$) be its first-passage matrices from $\ell(n)$ to $\ell(n-1)$, its first-return matrices to $\ell(n)$ under taboo of the lower levels, and its expected-visits matrices to $\ell(n)$ between two visits to the lower levels. Then for every $n\ge1$ the series $(I-U^{(n)})^{-1} = \sum_{\nu\ge0}(U^{(n)})^\nu$ converges entrywise, and
--   $$G^{(n)} = (I - U^{(n)})^{-1}A_2^{(n)}, \tag{12.3}$$
--   $$R^{(n)} = A_0^{(n-1)}(I - U^{(n)})^{-1}, \tag{12.4}$$
--   $$U^{(n)} = A_1^{(n)} + A_0^{(n)}G^{(n+1)}, \tag{12.5}$$
--   $$U^{(n)} = A_1^{(n)} + R^{(n+1)}A_2^{(n+1)}. \tag{12.6}$$
--   Thus any one of the three sequences determines the other two.
--
--   These relations are the level-dependent form of the relations between $G$, $U$ and $R$ of the homogeneous QBD, and they are the starting point of every algorithm for level-dependent QBDs.
--
--   **Formalization Note** The book prints (12.6) as $U^{(n)} = A_1^{(n)} + R^{(n+1)}A_2^{(n)}$. Since $R^{(n+1)}$ is a matrix from level $n$ to level $n+1$ and $A_2^{(n)}$ one from level $n$ to level $n-1$, that product is not defined when the levels have different sets of phases (and gives the wrong value when they do not); the statement here uses $A_2^{(n+1)}$, as in (12.8), (12.9) and the homogeneous relation $U = A_1 + RA_2$. In Lean $G^{(m+1)}$ is `matG P m`, $R^{(m+1)}$ is `matR P m`, $A_2^{(m+1)}$ is `A₂ m`, and products and series are evaluated in $[0,\infty]$, with $(I-U)^{-1}$ the series $\sum_\nu U^\nu$; its convergence is part of the conclusion.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 260, Theorem 12.1.2 (index typo in (12.6) corrected, finding F1)

import Mathlib
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Chain
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_QBD
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Passage

open scoped ENNReal

namespace MatrixAnalytic.Nonhomogeneous

/-- Theorem 12.1.2 (p. 260). For an irreducible nonhomogeneous QBD (12.1), the first-passage
matrices `G^{(m+1)} = matG P m`, the taboo first-return matrices `U^{(n)} = matU P n` and the
expected-visits matrices `R^{(m+1)} = matR P m` are related, for every level `n ≥ 1`, by
(12.3) `G^{(n)} = (I − U^{(n)})⁻¹ A₂^{(n)}`, (12.4) `R^{(n)} = A₀^{(n−1)} (I − U^{(n)})⁻¹`,
(12.5) `U^{(n)} = A₁^{(n)} + A₀^{(n)} G^{(n+1)}` and
(12.6) `U^{(n)} = A₁^{(n)} + R^{(n+1)} A₂^{(n+1)}`,
where `(I − U)⁻¹ := Σ_ν U^ν` and this series converges for every `n ≥ 1`. In (12.6) the book
prints `A₂^{(n)}`, which is not a well-defined product (finding F1); the only well-typed
reading, `A₂^{(n+1)}` (the argument `A₂ n`), is stated. Products and series are computed in
`ℝ≥0∞`. -/
theorem UGR_relations {ι : ℕ → Type*} [∀ n, Countable (ι n)] [∀ n, DecidableEq (ι n)]
    [∀ n, Nonempty (ι n)]
    (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ) (P : (Σ n, ι n) → (Σ n, ι n) → ℝ)
    (hPdef : P = ndqbdP A₀ A₁ A₂)
    (hP : IsStochasticC P) (hirr : IrreducibleC P) :
    (∀ n : ℕ, 1 ≤ n → ∀ i j, seriesInvE (matU P n) i j ≠ ⊤) ∧
    -- (12.3), at the level `m + 1`
    (∀ m : ℕ, matG P m = matMulE (seriesInvE (matU P (m + 1))) (ennMat (A₂ m))) ∧
    -- (12.4), at the level `m + 1`
    (∀ m : ℕ, matR P m = matMulE (ennMat (A₀ m)) (seriesInvE (matU P (m + 1)))) ∧
    -- (12.5), at the level `n ≥ 1`
    (∀ n : ℕ, 1 ≤ n → matU P n = ennMat (A₁ n) + matMulE (ennMat (A₀ n)) (matG P n)) ∧
    -- (12.6), at the level `n ≥ 1`, with `A₂^{(n+1)}`
    (∀ n : ℕ, 1 ≤ n → matU P n = ennMat (A₁ n) + matMulE (matR P n) (ennMat (A₂ n))) := by sorry

end MatrixAnalytic.Nonhomogeneous
