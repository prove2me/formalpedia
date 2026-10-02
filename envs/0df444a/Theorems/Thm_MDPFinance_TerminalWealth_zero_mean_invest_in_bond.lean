-- Prove2me | Theorems.Thm_MDPFinance_TerminalWealth_zero_mean_invest_in_bond
-- name    : MDPFinance.TerminalWealth.zero_mean_invest_in_bond
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:55:29.698519+00:00
-- url     : https://prove2.me/theorems/c2cd92e5-1fe1-49fb-93ac-a8c0398336a3
-- title:
--   Theorem 4.2.4 — zero-mean returns: invest all in the bond
-- statement:
--   If $\mathbb{E}R_n=0$ for every $n$: a) $V_n(x) = U(x S^0_N/S^0_n)$; b) $f_n^*(x)\equiv 0$ is
--   optimal — investing entirely in the bond is optimal whenever the risky assets carry no expected
--   excess return.
--
--   **Formalization Note (moderation).** Stated in the setting of Section 4.2 as the model
--   carries it (independent relative risks, no arbitrage, positive bond factors), with the
--   section's utility domain $[0,\infty)$ or $(0,\infty)$ and Assumption (FM)(ii) as explicit
--   hypotheses where the book uses them; the value function is $[-\infty,\infty)$-valued.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 82, PDF 96, Theorem 4.2.4

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Theorem 4.2.4 (Bäuerle–Rieder, p. 82, PDF 96). In the terminal wealth model of Section 4.2
(`𝔼‖R_n‖ < ∞`, `hFM2`), let `𝔼 R_n = 0` for `n = 1,…,N`. Then: a) the value functions are given
by `V_n(x) = U(x·S⁰_N/S⁰_n)` for `x ∈ E`; b) the optimal portfolio strategy `(f_0^*,…,f_{N-1}^*)`
is given by `f_n^*(x) ≡ 0` ("invest all the money in the bond"). -/
theorem zero_mean_invest_in_bond {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2)
    (hR_zero_mean : ∀ n, 1 ≤ n → n ≤ M.N → ∀ k, ∫ ω, M.R n ω k ∂M.measIP = 0) :
    (∀ n ≤ M.N, ∀ x ∈ M.domU, M.V n x = (M.U (x * M.S0 M.N / M.S0 n) : EReal)) ∧
      (∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
        (∀ n < M.N, ∀ x, fstar n x = 0) ∧
        ∀ x ∈ M.domU, M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.TerminalWealth
