-- Prove2me | Theorems.Thm_MDPFinance_TerminalWealth_exponential_utility_solution
-- name    : MDPFinance.TerminalWealth.exponential_utility_solution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:57:28.877728+00:00
-- url     : https://prove2.me/theorems/2f09ed7e-b9f1-4480-bdb4-b2728f1922a9
-- title:
--   Theorem 4.2.15 — exponential-utility closed form
-- statement:
--   Let $U(x) = -e^{-\gamma x}/\gamma$, $\gamma>0$. Then $V_n(x) = d_n\exp(-\gamma(S^0_N/S^0_n)x)$
--   with $d_N=-1/\gamma$, $d_n=(-1/\gamma)\sum_{k=n}^{N-1}v_k$; the optimal amounts $f_n^*(x)=a_n^*$
--   (the optimal solution of (4.13)) do **not** depend on the current wealth $x$.
--
--   **Formalization Note.** Relies on Theorem 4.1.1's extension to $\mathrm{dom}\,U=\mathbb{R}$
--   bounded above (Remark 4.1.2), since exponential utility has $\mathrm{dom}\,U=\mathbb{R}$; this
--   mission does not separately re-derive that extension (it carries no number of its own).
--
--   **Formalization Note (moderation).** $d_n = (-1/\gamma)\prod_{k=n}^{N-1} v_k$ (the recursion
--   $V_n = d_{n+1} v_n \exp(\cdot)$ multiplies the one-period values), and $v_k$ is the
--   Lebesgue-integral infimum of (4.13); no integrability of $R$ is assumed, as the book notes.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 91, PDF 105, Theorem 4.2.15

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market
import Definitions.Def_MDPFinance_TerminalWealth_ExpAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Theorem 4.2.15 (Bäuerle–Rieder, p. 91, PDF 105). Let `U` be the exponential utility,
`U(x) = -exp(-γx)/γ`, `γ > 0`, `domU = ℝ` (no integrability assumption on `R` is needed, only
the model's no-arbitrage assumption). Then: a) the value functions are
`V_n(x) = d_n exp(-γ(S⁰_N/S⁰_n)x)`, `x ∈ ℝ`, with `d_N = -1/γ` and
`d_n = (-1/γ) ∏_{k=n}^{N-1} v_k` (`v_k` the value of problem (4.13)); b) the optimal amounts
invested in the stocks are `f_n^*(x) = a_n^*`, `x ∈ ℝ`, where `a_n^*` is the optimal solution
of (4.13) and does not depend on `x`; the policy `(f_0^*,…,f_{N-1}^*)` is optimal. -/
theorem exponential_utility_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (γ : ℝ) (hγ : 0 < γ) (hdomU : M.domU = Set.univ)
    (hU : ∀ x : ℝ, M.U x = -Real.exp (-γ * x) / γ) :
    (∀ n ≤ M.N, ∀ x : ℝ,
        M.V n x = ((((-1 / γ) * ∏ k ∈ Finset.Ico n M.N, M.vExp γ k) *
          Real.exp (-γ * (M.S0 M.N / M.S0 n) * x) : ℝ) : EReal)) ∧
      (∃ astar : ℕ → (Fin d → ℝ),
        (∀ n < M.N,
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-γ * (M.S0 M.N / M.S0 n) *
            ∑ k, astar n k * M.R (n + 1) ω k)) ∂M.measIP).toReal = M.vExp γ n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x : ℝ, fstar n x = astar n) ∧
          ∀ x : ℝ, M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.TerminalWealth
