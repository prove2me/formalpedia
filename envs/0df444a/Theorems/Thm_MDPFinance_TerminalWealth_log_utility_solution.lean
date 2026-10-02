-- Prove2me | Theorems.Thm_MDPFinance_TerminalWealth_log_utility_solution
-- name    : MDPFinance.TerminalWealth.log_utility_solution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:57:40.860008+00:00
-- url     : https://prove2.me/theorems/84e8c6ff-a9b2-4c18-8738-5702de7c9ea3
-- title:
--   Theorem 4.2.13 — logarithmic-utility closed form
-- statement:
--   Let $U(x) = \log x$. Then $V_n(x) = \log x + d_n$ with $d_N=0$,
--   $d_n = \sum_{k=n}^{N-1}[\log(1+i_{k+1})+v_k]$; the optimal amounts are $f_n^*(x)=\alpha_n^*x$ for
--   the optimal solution $\alpha_n^*$ of (4.11).
--
--   **Formalization Note (moderation).** Stated in the setting of Section 4.2 as the model
--   carries it (independent relative risks, no arbitrage, positive bond factors), with the
--   section's utility domain $[0,\infty)$ or $(0,\infty)$ and Assumption (FM)(ii) as explicit
--   hypotheses where the book uses them; the value function is $[-\infty,\infty)$-valued.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 89, PDF 103, Theorem 4.2.13

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market
import Definitions.Def_MDPFinance_TerminalWealth_LogAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Theorem 4.2.13 (Bäuerle–Rieder, p. 89, PDF 103). Under Assumption (FM) (`hFM2`), let `U` be
the logarithmic utility, `U(x) = log x`, `domU = (0,∞)`. Then: a) the value functions are
`V_n(x) = log x + d_n`, `x > 0`, with `d_N = 0` and `d_n = Σ_{k=n}^{N-1} [log(1+i_{k+1}) + v_k]`
(`v_k` the value of problem (4.11)); b) the optimal amounts invested in the stocks are
`f_n^*(x) = α_n^* x`, `x > 0`, where `α_n^*` is the optimal solution of (4.11); the optimal
portfolio strategy is `(f_0^*,…,f_{N-1}^*)`. -/
theorem log_utility_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2) (hdomU : M.domU = Set.Ioi (0 : ℝ))
    (hU : ∀ x > (0 : ℝ), M.U x = Real.log x) :
    (∀ n ≤ M.N, ∀ x > (0 : ℝ),
        M.V n x = ((Real.log x +
          ∑ k ∈ Finset.Ico n M.N, (Real.log (1 + M.i (k + 1)) + M.vLog k) : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.AfracLog n ∧
          ∫ ω, Real.log (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ∂M.measIP = M.vLog n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x > (0 : ℝ), fstar n x = fun k => αstar n k * x) ∧
          ∀ x > (0 : ℝ), M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.TerminalWealth
