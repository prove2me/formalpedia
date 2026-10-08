-- Prove2me | Theorems.Thm_MDPFinance_ConsumptionInvestment_zero_mean_invest_in_bond_ci
-- name    : MDPFinance.ConsumptionInvestment.zero_mean_invest_in_bond_ci
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:00:58.33259+00:00
-- url     : https://prove2.me/theorems/d43aee2c-89fc-4327-b147-2177e6b17ade
-- title:
--   Theorem 4.3.5 — zero-mean returns: invest all in the bond
-- statement:
--   If $\mathbb{E}R_n=0$ for every $n$, the optimal investment $a_n^*(x)\equiv0$ — investing
--   entirely in the bond is optimal (the optimal consumption $c_n^*$ need not be trivial).
--
--   **Formalization Note (moderation).** Stated in the setting of Section 4.3 as the model carries
--   it (independent relative risks, no arbitrage, positive bond factors), with the section's
--   utility domain $[0,\infty)$ and Assumption (FM)(ii) as explicit hypotheses; the value function
--   is $[-\infty,\infty)$-valued.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 96, PDF 110, Theorem 4.3.5

import Mathlib
import Definitions.Def_MDPFinance_ConsumptionInvestment_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.ConsumptionInvestment

/-- Theorem 4.3.5 (Bäuerle–Rieder, p. 96, PDF 110). In the consumption-investment model of
Section 4.3 (`dom U_c = dom U_p = [0,∞)`, (FM)(ii) `hFM2`), let `𝔼 R_n = 0` for `n = 1,…,N`.
Then the optimal consumption-investment strategy `(f_0^*,…,f_{N-1}^*)`,
`f_n^*(x) = (c_n^*(x),a_n^*(x))`, has `a_n^*(x) ≡ 0` — investing all the money in the bond is the
optimal investment strategy (the optimal consumption `c_n^*` need not be trivial). -/
theorem zero_mean_invest_in_bond_ci {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : ConsumptionInvestmentMarket Ω d) (hdomU : M.domU = Set.Ici (0 : ℝ)) (hFM2 : M.FM2)
    (hR_zero_mean : ∀ n, 1 ≤ n → n ≤ M.N → ∀ k, ∫ ω, M.R n ω k ∂M.measIP = 0) :
    ∃ fstar : ℕ → ℝ → ℝ × (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
      (∀ n < M.N, ∀ x, (fstar n x).2 = 0) ∧
      ∀ x ∈ M.domU, M.Vpi fstar 0 x = M.V 0 x := by sorry

end MDPFinance.ConsumptionInvestment
