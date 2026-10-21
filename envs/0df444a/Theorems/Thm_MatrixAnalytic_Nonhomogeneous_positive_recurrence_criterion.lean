-- Prove2me | Theorems.Thm_MatrixAnalytic_Nonhomogeneous_positive_recurrence_criterion
-- name    : MatrixAnalytic.Nonhomogeneous.positive_recurrence_criterion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:54.751632+00:00
-- url     : https://prove2.me/theorems/f236c111-a82b-40a4-a42c-cb2c96fbd738
-- title:
--   Theorem 12.1.4 — positive recurrence iff (12.10)–(12.11) has a strictly positive solution
-- statement:
--   Let $P$ be the transition matrix (12.1) of a nonhomogeneous QBD that is stochastic and irreducible, every level having a nonempty countable set of phases, with first-passage matrix $G^{(1)}$ from $\ell(1)$ to $\ell(0)$ and expected-visits matrices $R^{(k)}$, $k\ge1$. Let $\mathbf 1$ be the column vector of ones.
--
--   1. The QBD is positive recurrent if and only if there is a row vector $\boldsymbol\pi_0$ on the phases of level $0$, with every entry strictly positive, such that
--   $$\boldsymbol\pi_0 = \boldsymbol\pi_0\big(A_1^{(0)} + A_0^{(0)}G^{(1)}\big) \tag{12.10}$$
--   and
--   $$\boldsymbol\pi_0\sum_{n\ge0}\prod_{1\le k\le n}R^{(k)}\mathbf 1 = 1, \tag{12.11}$$
--   where $\prod_{1\le k\le n}R^{(k)} = R^{(1)}\cdots R^{(n)}$ and the empty product ($n=0$) is the identity.
--   2. The system (12.10) is equivalent to the system $\boldsymbol\pi_0 = \boldsymbol\pi_0\big(A_1^{(0)} + R^{(1)}A_2^{(1)}\big)$: a nonnegative vector solves one if and only if it solves the other.
--
--   Together with Theorem 12.1.1 this completes the description of the stationary distribution: $\boldsymbol\pi_0$ is the stationary vector of the chain watched on level $0$, normalized so that the whole matrix-product vector sums to one.
--
--   **Formalization Note** $G^{(1)}$ is `matG P 0`, $R^{(k+1)}$ is `matR P k` and $A_2^{(1)}$ is `A₂ 0`. Products, the ordered products $R^{(1)}\cdots R^{(n)}$ and the series are evaluated in $[0,\infty]$. The equivalence in part 2 is stated for nonnegative vectors, the only ones for which these products are evaluated. Positive recurrence means that every state has a finite expected return time.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 262, Theorem 12.1.4

import Mathlib
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Chain
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_QBD
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Passage

open scoped ENNReal

namespace MatrixAnalytic.Nonhomogeneous

/-- Theorem 12.1.4 (p. 262). Let the nonhomogeneous QBD (12.1) be irreducible, with
`G^{(1)} = matG P 0` and `R^{(k+1)} = matR P k`.
1. The QBD is positive recurrent if and only if there is a strictly positive row vector `π₀`
   on the phases of level `0` with (12.10) `π₀ = π₀ (A₁^{(0)} + A₀^{(0)} G^{(1)})`, normalized by
   (12.11) `π₀ Σ_{n ≥ 0} Π_{1 ≤ k ≤ n} R^{(k)} 1 = 1` (the empty product, `n = 0`, being the
   identity matrix).
2. The system (12.10) is equivalent to `π₀ = π₀ (A₁^{(0)} + R^{(1)} A₂^{(1)})`: a nonnegative
   vector solves one if and only if it solves the other.
Vector–matrix products, the ordered products `R^{(1)} ⋯ R^{(n)}` (`levelProdE`) and the series
are computed in `ℝ≥0∞`. -/
theorem positive_recurrence_criterion {ι : ℕ → Type*} [∀ n, Countable (ι n)]
    [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ) (P : (Σ n, ι n) → (Σ n, ι n) → ℝ)
    (hPdef : P = ndqbdP A₀ A₁ A₂)
    (hP : IsStochasticC P) (hirr : IrreducibleC P) :
    ((∀ x : Σ n, ι n, PositiveRecurrent P x) ↔
      ∃ π₀ : ι 0 → ℝ, (∀ i, 0 < π₀ i) ∧
        -- (12.10)
        (∀ j : ι 0, ENNReal.ofReal (π₀ j) =
          vecMulE (fun i => ENNReal.ofReal (π₀ i))
            (ennMat (A₁ 0) + matMulE (ennMat (A₀ 0)) (matG P 0)) j) ∧
        -- (12.11)
        ∑' n : ℕ, ∑' j : ι n,
          vecMulE (fun i => ENNReal.ofReal (π₀ i)) (levelProdE (matR P) n) j = 1) ∧
    ∀ π₀ : ι 0 → ℝ, (∀ i, 0 ≤ π₀ i) →
      ((∀ j : ι 0, ENNReal.ofReal (π₀ j) =
          vecMulE (fun i => ENNReal.ofReal (π₀ i))
            (ennMat (A₁ 0) + matMulE (ennMat (A₀ 0)) (matG P 0)) j) ↔
        ∀ j : ι 0, ENNReal.ofReal (π₀ j) =
          vecMulE (fun i => ENNReal.ofReal (π₀ i))
            (ennMat (A₁ 0) + matMulE (matR P 0) (ennMat (A₂ 0))) j) := by sorry

end MatrixAnalytic.Nonhomogeneous
