-- Prove2me | Theorems.Thm_MatrixAnalytic_Nonhomogeneous_limiting_matrix_product
-- name    : MatrixAnalytic.Nonhomogeneous.limiting_matrix_product
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:50.372038+00:00
-- url     : https://prove2.me/theorems/7fddba2f-2925-45c3-aaa2-500fad89072b
-- title:
--   Theorem 12.1.1 — the limiting distribution has the matrix-product form π_n = π_{n−1} R⁽ⁿ⁾
-- statement:
--   Let $P$ be the transition matrix (12.1) of a nonhomogeneous QBD, stochastic, irreducible, aperiodic and positive recurrent, every level having a nonempty countable set of phases. Let $\boldsymbol\pi$ be its limiting probability vector, $\pi_y = \lim_{t\to\infty}\mathrm P[X_t = y\mid X_0 = x]$ for all states $x,y$, and write $\boldsymbol\pi_n = (\pi_{(n,i)})_{i}$ for its restriction to level $n$. For $n\ge1$ let $R^{(n)}_{ij}$ be the expected number of visits to $(n,j)$, starting from $(n-1,i)$, before the first return to the levels $\ell(0)\cup\dots\cup\ell(n-1)$. Then every entry of $R^{(n)}$ is finite and
--   $$\boldsymbol\pi_n = \boldsymbol\pi_{n-1}R^{(n)} \qquad\text{for } n\ge1. \tag{12.2}$$
--
--   Consequently $\boldsymbol\pi_n = \boldsymbol\pi_0R^{(1)}R^{(2)}\cdots R^{(n)}$: the stationary distribution of a level-dependent QBD has a matrix-product form, the analogue of the matrix-geometric form $\boldsymbol\pi_n = \boldsymbol\pi_0R^n$ of the homogeneous case.
--
--   **Formalization Note** $R^{(m+1)}$ is `matR P m`, and the vector–matrix product is evaluated in $[0,\infty]$ on the nonnegative entries of $\boldsymbol\pi$. "Limiting probability vector" is taken literally, as the entrywise limit of the $t$-step transition probabilities from every initial state.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 260, Theorem 12.1.1

import Mathlib
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Chain
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_QBD
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Passage

open scoped ENNReal

namespace MatrixAnalytic.Nonhomogeneous

/-- Theorem 12.1.1 (p. 260). Let the nonhomogeneous QBD (12.1) be irreducible, aperiodic and
positive recurrent, and let `π` be its limiting probability vector,
`π_y = lim_{t → ∞} P[X_t = y | X_0 = x]` for all states `x, y`. Then
(12.2) `π_n = π_{n−1} R^{(n)}` for `n ≥ 1`, where `R^{(m+1)} = matR P m` records the expected
number of visits to the states of level `m + 1` between two visits to the levels
`ℓ(0) ∪ ⋯ ∪ ℓ(m)`; the entries of every `R^{(n)}` are finite. The vector–matrix product is
computed in `ℝ≥0∞`. -/
theorem limiting_matrix_product {ι : ℕ → Type*} [∀ n, Countable (ι n)]
    [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ) (P : (Σ n, ι n) → (Σ n, ι n) → ℝ)
    (hPdef : P = ndqbdP A₀ A₁ A₂)
    (hP : IsStochasticC P) (hirr : IrreducibleC P) (haper : AperiodicC P)
    (hpos : ∀ x : Σ n, ι n, PositiveRecurrent P x)
    (π : (Σ n, ι n) → ℝ)
    (hlim : ∀ x y : Σ n, ι n,
      Filter.Tendsto (fun t => stepPow P t x y) Filter.atTop (nhds (π y))) :
    (∀ m : ℕ, ∀ i j, matR P m i j ≠ ⊤) ∧
    -- (12.2), at the level `m + 1 ≥ 1`
    ∀ m : ℕ, ∀ j : ι (m + 1), ENNReal.ofReal (π ⟨m + 1, j⟩) =
      vecMulE (fun i : ι m => ENNReal.ofReal (π ⟨m, i⟩)) (matR P m) j := by sorry

end MatrixAnalytic.Nonhomogeneous
