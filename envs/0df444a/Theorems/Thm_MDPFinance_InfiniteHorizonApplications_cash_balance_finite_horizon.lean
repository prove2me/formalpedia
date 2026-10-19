-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_cash_balance_finite_horizon
-- name    : MDPFinance.InfiniteHorizonApplications.cash_balance_finite_horizon
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T04:44:40.491+00:00
-- url     : https://prove2.me/theorems/9f590e6e-c0e2-49d1-bfdb-4c3390d786a7
-- title:
--   Cash balance: convex finite-horizon values and optimal critical levels
-- statement:
--   Consider the cash-balance model with positive transfer rates $c_u,c_d$, discount $0<\beta<1$, an integrable cash change $Z$, and nonnegative convex holding cost $L$ satisfying $L(0)=0$ and superlinear growth in both directions. Let $J_n(x)$ be the infimum, over measurable Markov policies, of the expected $n$-period discounted cost, with $J_0=0$.
--
--   For every horizon $n$, the finite real-valued conversion of $J_n$ is convex. There are critical-level sequences $S_n^-,S_n^+$, ordered for every $n\ge1$, such that
--   $$
--   J_n(x)=\begin{cases}
--   (S_n^- -x)c_u+L(S_n^-)+\beta\mathbb E[J_{n-1}(S_n^- -Z)],&x<S_n^-,\\
--   L(x)+\beta\mathbb E[J_{n-1}(x-Z)],&S_n^-\le x\le S_n^+,\\
--   (x-S_n^+)c_d+L(S_n^+)+\beta\mathbb E[J_{n-1}(S_n^+ -Z)],&x>S_n^+.
--   \end{cases}
--   $$
--   This is the finite-horizon threshold structure of Theorem 2.6.2. It supplies the finite-horizon input for passing jointly converging critical levels to the infinite-horizon limit. It makes no assertion about convergence of the levels or infinite-horizon optimality.
--
--   **Formalization Note** Costs and expectations use extended nonnegative reals; convexity is stated after conversion to real values. Horizon-zero critical levels are unconstrained.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Springer 2011, DOI 10.1007/978-3-642-18324-9, §2.6.2, Theorem 2.6.2, pp. 46–47 (PDF pp. 61–62), finite-horizon cash-balance critical-level formula. https://link.springer.com/chapter/10.1007/978-3-642-18324-9_2

import Definitions.Def_MDPFinance_InfiniteHorizonApplications_CashBalance

open MeasureTheory ProbabilityTheory MDPFinance.InfiniteHorizonApplications

theorem MDPFinance.InfiniteHorizonApplications.cash_balance_finite_horizon (Mk : CashBalanceMarket) :
    (∀ n, ConvexOn ℝ Set.univ (fun x => (Mk.Jn n x).toReal)) ∧
      (∃ Sminus Splus : ℕ → ℝ,
        (∀ n, 1 ≤ n → Sminus n ≤ Splus n ∧ ∀ x, Mk.Jn n x =
          if x < Sminus n then
            ENNReal.ofReal ((Sminus n - x) * Mk.cu + Mk.L (Sminus n)) +
              ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n - 1) (Sminus n - z) ∂Mk.μZ
          else if x ≤ Splus n then
            ENNReal.ofReal (Mk.L x) + ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n - 1) (x - z) ∂Mk.μZ
          else
            ENNReal.ofReal ((x - Splus n) * Mk.cd + Mk.L (Splus n)) +
              ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n - 1) (Splus n - z) ∂Mk.μZ)) := by sorry
