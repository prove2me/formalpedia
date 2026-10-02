-- Prove2me | Theorems.Thm_MDPFinance_TerminalWealth_power_utility_solution
-- name    : MDPFinance.TerminalWealth.power_utility_solution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:57:26.035973+00:00
-- url     : https://prove2.me/theorems/2e27fc85-aad5-4145-bbea-76d8dd63822e
-- title:
--   Theorem 4.2.6 — power-utility closed form
-- statement:
--   Let $U(x) = x^\gamma/\gamma$, $0<\gamma<1$. Then $V_n(x) = d_n x^\gamma$ with $d_N=1/\gamma$,
--   $d_n = (1/\gamma)\prod_{k=n}^{N-1}(1+i_{k+1})^\gamma v_k$; the optimal amounts are
--   $f_n^*(x) = \alpha_n^* x$ for the optimal solution $\alpha_n^*$ of (4.7).
--
--   **Formalization Note (moderation).** Stated in the setting of Section 4.2 as the model
--   carries it (independent relative risks, no arbitrage, positive bond factors), with the
--   section's utility domain $[0,\infty)$ or $(0,\infty)$ and Assumption (FM)(ii) as explicit
--   hypotheses where the book uses them; the value function is $[-\infty,\infty)$-valued.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 83, PDF 97, Theorem 4.2.6

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market
import Definitions.Def_MDPFinance_TerminalWealth_PowerAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Theorem 4.2.6 (Bäuerle–Rieder, p. 83, PDF 97). Under Assumption (FM) (`hFM2`), let `U` be
the power utility, `U(x) = x^γ/γ`, `domU = [0,∞)`, `0 < γ < 1`. Then: a) the value functions are
`V_n(x) = d_n x^γ`, `x ≥ 0`, with `d_N = 1/γ` and `d_n = (1/γ) ∏_{k=n}^{N-1} (1+i_{k+1})^γ v_k`;
b) the optimal amounts invested in the stocks are `f_n^*(x) = α_n^* x`, `x ≥ 0`, where `α_n^*`
is the optimal solution of (4.7); the optimal portfolio strategy is `(f_0^*,…,f_{N-1}^*)`. -/
theorem power_utility_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hdomU : M.domU = Set.Ici (0 : ℝ)) (hU : ∀ x ≥ (0 : ℝ), M.U x = x ^ γ / γ) :
    (∀ n ≤ M.N, ∀ x ≥ (0 : ℝ),
        M.V n x = ((((1 / γ) * ∏ k ∈ Finset.Ico n M.N, ((1 + M.i (k + 1)) ^ γ * M.vPower γ k)) *
          x ^ γ : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.Afrac n ∧
          ∫ ω, (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ^ γ ∂M.measIP = M.vPower γ n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x ≥ (0 : ℝ), fstar n x = fun k => αstar n k * x) ∧
          ∀ x ≥ (0 : ℝ), M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.TerminalWealth
