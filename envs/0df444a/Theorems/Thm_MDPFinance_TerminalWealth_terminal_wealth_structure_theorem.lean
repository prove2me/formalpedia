-- Prove2me | Theorems.Thm_MDPFinance_TerminalWealth_terminal_wealth_structure_theorem
-- name    : MDPFinance.TerminalWealth.terminal_wealth_structure_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:55:34.558271+00:00
-- url     : https://prove2.me/theorems/38f6e8dd-90be-4084-a7a3-5831897b034f
-- title:
--   Theorem 4.2.2 — the terminal wealth structure theorem (goal)
-- statement:
--   For the multiperiod terminal wealth problem: a) $V_n$ is strictly increasing, strictly concave
--   and continuous; b) $V_N = U$, $V_n(x) = \sup_{a \in D_n(x)} \mathbb{E}[V_{n+1}((1+i_{n+1})(x+
--   a\cdot R_{n+1}))]$; c) maximizers $f_n^*$ of $V_{n+1}$ exist and $(f_0^*,\dots,f_{N-1}^*)$ is
--   optimal.
--
--   **Formalization Note.** Part (c)'s "optimal for the $N$-stage problem" is the strongest
--   available comparison: the induced strategy attains $V_0$ itself (`Vpi fstar 0 x = V 0 x`), not
--   merely a one-step optimality property.
--
--   **Formalization Note (moderation).** Stated in the setting of Section 4.2 as the model
--   carries it (independent relative risks, no arbitrage, positive bond factors), with the
--   section's utility domain $[0,\infty)$ or $(0,\infty)$ and Assumption (FM)(ii) as explicit
--   hypotheses where the book uses them; the value function is $[-\infty,\infty)$-valued.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 81, PDF 95, Theorem 4.2.2

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Theorem 4.2.2 (Bäuerle–Rieder, p. 81, PDF 95) — the goal of this mission. For the
multiperiod terminal wealth problem of Section 4.2 (utility with `domU = [0,∞)` or `(0,∞)`,
independent relative risks, Assumption (FM): no arbitrage and `𝔼‖R_n‖ < ∞`) it holds: a) the
value functions `V_n` are strictly increasing, strictly concave and continuous; b) the Bellman
equation `V_N(x) = U(x)`, `V_n(x) = sup_{a ∈ D_n(x)} 𝔼[V_{n+1}((1+i_{n+1})(x+a·R_{n+1}))]` holds;
c) there exist maximizers `f_n^*` of `V_{n+1}`, and the portfolio strategy `(f_0^*,…,f_{N-1}^*)`
is optimal for the `N`-stage terminal wealth problem. -/
theorem terminal_wealth_structure_theorem {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d)
    (hdomU : M.domU = Set.Ici (0 : ℝ) ∨ M.domU = Set.Ioi (0 : ℝ)) (hFM2 : M.FM2) :
    (∀ n ≤ M.N, StrictMonoOn (M.V n) M.domU ∧ StrictConcaveOnEReal M.domU (M.V n) ∧
        ContinuousOn (M.V n) M.domU) ∧
      (∀ x ∈ M.domU, M.V M.N x = (M.U x : EReal)) ∧
      (∀ n < M.N, ∀ x ∈ M.domU,
        M.V n x = ⨆ a ∈ M.D n x, erealIntegral M.measIP (fun ω => M.V (n + 1)
          ((1 + M.i (n + 1)) * (x + ∑ k, a k * M.R (n + 1) ω k)))) ∧
      (∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
        (∀ n < M.N, ∀ x ∈ M.domU,
          erealIntegral M.measIP (fun ω => M.V (n + 1)
            ((1 + M.i (n + 1)) * (x + ∑ k, fstar n x k * M.R (n + 1) ω k))) = M.V n x) ∧
        ∀ x ∈ M.domU, M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.TerminalWealth
