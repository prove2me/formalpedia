-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_cash_balance_critical_limit_formula
-- name    : MDPFinance.InfiniteHorizonApplications.cash_balance_critical_limit_formula
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T04:32:46.72174+00:00
-- url     : https://prove2.me/theorems/58e83552-1ddb-43fc-a867-baa63678d86e
-- title:
--   Cash balance: finite-horizon critical levels and their limiting value formula
-- statement:
--   Let a cash-balance market have positive transfer rates $c_u,c_d$, a nonnegative convex holding cost $L$ with $L(0)=0$ and $L(x)/|x|\to\infty$ in both directions, an integrable cash change $Z$, and discount factor $0<\beta<1$. Write $J_n$ for its minimal $n$-period cost and
--   $$
--   J(x)=\sup_{n\ge0}J_n(x).
--   $$
--   The finite-horizon values, viewed as real functions, are convex. There are critical-level sequences $S_n^-\le S_n^+$ for every $n\ge1$ such that, with $J_0=0$,
--   $$
--   J_n(x)=\begin{cases}
--   (S_n^- -x)c_u+L(S_n^-)+\beta\mathbb E[J_{n-1}(S_n^- -Z)],&x<S_n^-,\\
--   L(x)+\beta\mathbb E[J_{n-1}(x-Z)],&S_n^-\le x\le S_n^+,\\
--   (x-S_n^+)c_d+L(S_n^+)+\beta\mathbb E[J_{n-1}(S_n^+ -Z)],&x>S_n^+.
--   \end{cases}
--   $$
--   For every strictly increasing subsequence of horizons along which these two levels converge jointly to $(s,t)$, the same three-region identity holds with $J_n,J_{n-1},S_n^-,S_n^+$ replaced by $J,J,s,t$.
--
--   This is the critical-level analysis in Theorems 2.6.2 and 7.6.1. It separates the finite-horizon formulas and their passage to the limit from infinite-horizon policy verification. The existence of a common convergent subsequence, finiteness of the values, equality of $J$ with the infinite-horizon minimum, and optimality of the limiting stationary rule are not conclusions of this lemma.
--
--   **Formalization Note** Costs and expectations use extended nonnegative reals. Real convexity uses their real-valued conversions. The limiting piecewise formula uses the conditions $x<s$, then $x\le t$, as in the finite-horizon formula.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Springer 2011, DOI 10.1007/978-3-642-18324-9, §2.6.2, Theorem 2.6.2, and §7.6.2, Theorem 7.6.1 (p. 225), critical-level formulas and passage to the limit. https://link.springer.com/chapter/10.1007/978-3-642-18324-9_7

import Definitions.Def_MDPFinance_InfiniteHorizonApplications_CashBalance

open MeasureTheory ProbabilityTheory MDPFinance.InfiniteHorizonApplications

theorem MDPFinance.InfiniteHorizonApplications.cash_balance_critical_limit_formula (Mk : CashBalanceMarket) :
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
              ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jn (n - 1) (Splus n - z) ∂Mk.μZ) ∧
        ∀ (φ : ℕ → ℕ) (Sm Sp : ℝ), StrictMono φ →
          Filter.Tendsto (Sminus ∘ φ) Filter.atTop (nhds Sm) →
          Filter.Tendsto (Splus ∘ φ) Filter.atTop (nhds Sp) →
          (∀ x, Mk.Jlim x =
            if x < Sm then
              ENNReal.ofReal ((Sm - x) * Mk.cu + Mk.L Sm) +
                ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jlim (Sm - z) ∂Mk.μZ
            else if x ≤ Sp then
              ENNReal.ofReal (Mk.L x) + ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jlim (x - z) ∂Mk.μZ
            else
              ENNReal.ofReal ((x - Sp) * Mk.cd + Mk.L Sp) +
                ENNReal.ofReal Mk.β * ∫⁻ z, Mk.Jlim (Sp - z) ∂Mk.μZ)) := by sorry
