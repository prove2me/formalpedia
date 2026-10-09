-- Prove2me | Theorems.Thm_ModernOnlineLearning_Portfolio_theorem_10_1_uniform
-- name    : ModernOnlineLearning.Portfolio.theorem_10_1_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:38:54.885802+00:00
-- url     : https://prove2.me/theorems/fe473b1d-f3b8-4da7-aaf8-c14a5416afcb
-- title:
--   Theorem 10.1, pp. 172–173 — the uniform-prior portfolio has logarithmic regret
-- statement:
--   Consider a market with $d\ge2$ stocks and a horizon $T\ge1$. Let each market-gain vector $w_t$ be nonnegative and nonzero. Algorithm 10.1 uses the uniform probability prior $F_d$ on the portfolio simplex, and its realized wealth is $W_T>0$. For every constantly rebalanced portfolio $u\in\Delta^{d-1}$ with $W_T(u)>0$,
--
--   $$\log W_T(u)-\log W_T\le\log\binom{T+d-1}{d-1}\le(d-1)\left[\log\left(\frac{T}{d-1}+1\right)+1\right].$$
--
--   Thus the log-wealth shortfall to the best fixed allocation grows only logarithmically with the horizon, without upper or lower bounds on the positive market gains.
--
--   **Formalization Note** Portfolios with $W_T(u)=0$ have log wealth $-\infty$ in the book; Lean’s real logarithm is total and assigns zero to $\log 0$, so the real-log inequality is stated for positive-wealth comparators. The theorem asserts that the algorithm’s wealth is positive. The prior is fixed by its uniform coordinate density, and the portfolio is the exact integral-ratio strategy.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 10.1, uniform-prior bullet, pp. 172–173; proof p. 176

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Setting
set_option autoImplicit false

namespace ModernOnlineLearning.Portfolio

/-- Theorem 10.1, uniform-prior bullet, pp. 172-173. Comparator portfolios of
zero wealth have logarithmic wealth `-∞` in the book, so the real-log inequality
is stated on the positive-wealth comparators. -/
theorem theorem_10_1_uniform {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T)
    (w : ℕ → Fin d → ℝ)
    (hw_nonneg : ∀ t ∈ Finset.Icc 1 T, ∀ i, 0 ≤ w t i)
    (hw_ne : ∀ t ∈ Finset.Icc 1 T, w t ≠ 0) :
    0 < portfolioWealth w (weightedPortfolio (uniformPrior d) w) T ∧
    (∀ u ∈ stdSimplex ℝ (Fin d), 0 < wealthCRP w u T →
      Real.log (wealthCRP w u T) -
        Real.log (portfolioWealth w (weightedPortfolio (uniformPrior d) w) T) ≤
          Real.log (((T + d - 1).choose (d - 1) : ℕ) : ℝ)) ∧
    Real.log (((T + d - 1).choose (d - 1) : ℕ) : ℝ) ≤
      ((d - 1 : ℕ) : ℝ) *
        (Real.log ((T : ℝ) / ((d - 1 : ℕ) : ℝ) + 1) + 1) := by sorry

end ModernOnlineLearning.Portfolio
