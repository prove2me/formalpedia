-- Prove2me | Theorems.Thm_MDPFinance_ConsumptionInvestment_consumption_investment_structure_theorem
-- name    : MDPFinance.ConsumptionInvestment.consumption_investment_structure_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:00:47.838658+00:00
-- url     : https://prove2.me/theorems/1d94ffec-d415-4564-8191-44d3cbdf6510
-- title:
--   Theorem 4.3.3 — the consumption-investment structure theorem (goal)
-- statement:
--   a) $V_n$ is strictly increasing, strictly concave and continuous; b) $V_N=U_p$, $V_n(x) =
--   \sup_{(c,a)\in D_n(x)}[U_c(c) + \mathbb{E}V_{n+1}((1+i_{n+1})(x-c+a\cdot R_{n+1}))]$; c)
--   maximizers $f_n^*$ of $V_{n+1}$ exist and $(f_0^*,\dots,f_{N-1}^*)$ is optimal.
--
--   **Formalization Note (moderation).** Stated in the setting of Section 4.3 as the model carries
--   it (independent relative risks, no arbitrage, positive bond factors), with the section's
--   utility domain $[0,\infty)$ and Assumption (FM)(ii) as explicit hypotheses; the value function
--   is $[-\infty,\infty)$-valued.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 95, PDF 109, Theorem 4.3.3

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- Theorem 4.3.3 (Bäuerle–Rieder, p. 95, PDF 109) — the goal of this mission. For the
multiperiod consumption-investment problem of Section 4.3 (`dom U_c = dom U_p = [0,∞)`,
Assumption (FM): no arbitrage in the model and `𝔼‖R_n‖ < ∞`, `hFM2`): a) `V_n` is strictly
increasing, strictly concave and continuous; b) `V_N(x) = U_p(x)`,
`V_n(x) = sup_{(c,a) ∈ D_n(x)} [U_c(c) + 𝔼 V_{n+1}((1+i_{n+1})(x-c+a\cdot R_{n+1}))]`;
c) maximizers `f_n^*` of `V_{n+1}` exist and `(f_0^*,…,f_{N-1}^*)` is optimal for the `N`-stage
problem. -/
theorem consumption_investment_structure_theorem {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : ConsumptionInvestmentMarket Ω d) (hdomU : M.domU = Set.Ici (0 : ℝ)) (hFM2 : M.FM2) :
    (∀ n ≤ M.N, StrictMonoOn (M.V n) M.domU ∧ StrictConcaveOnEReal M.domU (M.V n) ∧
        ContinuousOn (M.V n) M.domU) ∧
      (∀ x ∈ M.domU, M.V M.N x = (M.Up x : EReal)) ∧
      (∀ n < M.N, ∀ x ∈ M.domU,
        M.V n x = ⨆ ca ∈ M.D n x,
          (M.Uc ca.1 : EReal) + erealIntegral M.measIP (fun ω => M.V (n + 1) ((1 + M.i (n + 1)) *
            (x - ca.1 + ∑ k, ca.2 k * M.R (n + 1) ω k)))) ∧
      (∃ fstar : ℕ → ℝ → ℝ × (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
        (∀ n < M.N, ∀ x ∈ M.domU,
          (M.Uc (fstar n x).1 : EReal) + erealIntegral M.measIP (fun ω => M.V (n + 1)
            ((1 + M.i (n + 1)) * (x - (fstar n x).1 + ∑ k, (fstar n x).2 k * M.R (n + 1) ω k))) =
            M.V n x) ∧
        ∀ x ∈ M.domU, M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.ConsumptionInvestment
