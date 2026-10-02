-- Prove2me | Theorems.Thm_MDPFinance_IndifferencePricing_index_tracking_solution
-- name    : MDPFinance.IndifferencePricing.index_tracking_solution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:11:34.317984+00:00
-- url     : https://prove2.me/theorems/86e5e467-d14b-4372-9f77-a0eb01f461e3
-- title:
--   Theorem 4.8.1 — explicit LQ solution of the index-tracking problem
-- statement:
--   a) The value functions of problem (4.36) are $V_n(x,\hat s) = (x,\hat s)Q_n(x,\hat
--   s)^\top$ where $(Q_n)$ satisfies the Riccati-type recursion of Theorem 2.6.3
--   (`QRecursion`); the $Q_n$ are symmetric and positive semidefinite. b) The optimal portfolio
--   strategy $\pi^*=(f_0^*,\dots,f_{N-1}^*)$ is linear,
--   $$f_n^*(x,\hat s) = -\big(\mathbb{E}[B_{n+1}^\top Q_{n+1}B_{n+1}]\big)^{-1}
--   \mathbb{E}[B_{n+1}^\top Q_{n+1}A_{n+1}]\,(x,\hat s)^\top.$$
--
--   This is the section's payoff: the index-tracking problem is exactly an instance of the general
--   stochastic linear-quadratic problem solved once, abstractly, in Theorem 2.6.3, so no new Bellman
--   argument is needed here — only the identification of this problem's own $A_{n+1},B_{n+1},Q$.
--
--   **Formalization Note.** The optimal policy is genuinely linear in *both* coordinates $(x,\hat
--   s)$ of the state, not just the wealth $x$ — dropping the $\hat s$-dependence would misstate an
--   index-tracking policy as an ordinary terminal-wealth policy, this chunk's flagged pitfall.
--
--   **Moderation note.** The value claims are on the state space $E=\mathbb{R}\times\mathbb{R}_+$ ($\hat s\ge 0$) and compare the $[0,\infty]$-valued cost with $(x,\hat s)Q_n(x,\hat s)^\top$. The optimal decision rule is stated in Theorem 2.6.3(b)'s form $-(\mathbb{E}[B^\top Q_{n+1}B])^{-1}\mathbb{E}[B^\top Q_{n+1}A]$, which equals the book's printed formula because $B_{n+1}^\top Q_{n+1}B_{n+1}=(1+i_{n+1})^2q^{11}_{n+1}R_{n+1}R_{n+1}^\top$; the inverse is genuine under the market's regularity field.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 134, PDF 148, Theorem 4.8.1

import Mathlib
import Definitions.Def_MDPFinance_IndifferencePricing_IndexTrackingMarket
import Definitions.Def_MDPFinance_IndifferencePricing_IndexTrackingRiccati

open MeasureTheory ProbabilityTheory Matrix

namespace MDPFinance.IndifferencePricing

/-- Theorem 4.8.1 (Bäuerle–Rieder, p. 134, PDF 148). a) The value functions of problem (4.36) are
given by `V_n(x,ŝ) = (x,ŝ)Q_n(x,ŝ)ᵀ` where `(Q_n)` satisfy the Riccati-type recursion of Theorem
2.6.3; `Q_n` are symmetric and positive semidefinite. b) The optimal portfolio strategy
`π^* = (f_0^*,…,f_{N-1}^*)` is linear, `f_n^*(x,ŝ) = -(𝔼[B_{n+1}ᵀQ_{n+1}B_{n+1}])⁻¹
𝔼[B_{n+1}ᵀQ_{n+1}A_{n+1}](x,ŝ)ᵀ` (Theorem 2.6.3(b)'s form; it equals the book's printed
`-(𝔼[R_{n+1}R_{n+1}ᵀ])⁻¹ 𝔼[(R_{n+1}, q²¹_{n+1}/((1+i_{n+1})q¹¹_{n+1}) R̂_{n+1}R_{n+1})](x,ŝ)ᵀ`
since `B_{n+1}ᵀQ_{n+1}B_{n+1} = (1+i_{n+1})² q¹¹_{n+1} R_{n+1}R_{n+1}ᵀ`). Values are the
`ℝ≥0∞`-valued costs of `IndexTrackingMarket.V`; the state claims are made on the state space
`E = ℝ × ℝ₊`. -/
theorem index_tracking_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : IndexTrackingMarket Ω d) :
    ∃ Q : ℕ → Matrix (Fin 2) (Fin 2) ℝ, M.QRecursion Q ∧
      (∀ n, (Q n).IsSymm) ∧ (∀ n, (Q n).PosSemidef) ∧
      (∀ n ≤ M.N, ∀ x ŝ : ℝ, 0 ≤ ŝ →
        M.V n x ŝ = ENNReal.ofReal (![x, ŝ] ⬝ᵥ (Q n).mulVec ![x, ŝ])) ∧
      (∃ fstar : ℕ → ℝ × ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
        (∀ n < M.N, ∀ x ŝ : ℝ, fstar n (x, ŝ) =
          -((matExpect M.measIP (fun ω => (M.Bmat n ω)ᵀ * Q (n + 1) * M.Bmat n ω))⁻¹).mulVec
            ((matExpect M.measIP (fun ω => (M.Bmat n ω)ᵀ * Q (n + 1) * M.Amat n ω)).mulVec
              ![x, ŝ])) ∧
        ∀ x ŝ : ℝ, 0 ≤ ŝ → M.Vpi fstar x ŝ = M.V 0 x ŝ) := by sorry

end MDPFinance.IndifferencePricing
