-- Prove2me | Theorems.Thm_MultitierCSR_Strategy_theorem_1
-- name    : MultitierCSR.Strategy.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:06.787731+00:00
-- url     : https://prove2.me/theorems/d79134fe-19d3-4df7-affd-9214140e90a4
-- title:
--   Theorem 1, pp. 14–15 — buyer's optimal control, delegation, or no effort
-- statement:
--   Consider the three-tier sequential responsibility-effort game under its standing parameter assumptions. Tier 2 maximizes its profit after every feasible earlier history, Tier 1 maximizes its profit anticipating Tier 2, and the buyer maximizes its resulting profit over all nonnegative efforts, selecting positive effort over zero in a tie. No buyer-optimal outcome has both the buyer and Tier 1 exerting positive effort.
--
--   With $\tau_i=k_i/\ell_i$ and $g(\tau_0)=\bigl(b\tau_0/(2\sqrt{\tau_0}-\sqrt{\tau_1})\bigr)^2$, the selected equilibrium is the control, delegation, or no-effort row of Table 2 as follows:
--
--   1. If $\tau_1<\tau_2/b^2$: control for $\tau_0\le\tau_1/4$; when $\tau_1/4<\tau_0\le\tau_1$, control for $\tau_2\le g(\tau_0)$ and delegation otherwise; delegation for $\tau_0>\tau_1$.
--   2. If $\tau_1\ge\tau_2/b^2$: control for $\tau_0\le\tau_2/b^2$, and no effort otherwise.
--
--   Each row gives the unique selected buyer optimum, the induced efforts of both suppliers, and the actual violation probability $\lambda$. The detected violation probability is $\alpha=\beta\lambda$, yielding Table 2's last column. The theorem characterizes the equilibrium of the underlying best-response game, rather than comparing predefined row formulas.
--
--   **Formalization Note** The standing regime makes explicit $d>0$, $a_i\ge0$, $\ell_i>0$, and $\beta>0$. Efforts are nonnegative. The tie convention selects control at $\tau_2=g(\tau_0)$.
-- source:
--   Huang, Song & Swinney, Managing Social Responsibility in Multitier Supply Chains, SSRN 2837332 (version of October 2021), pp. 14–15 (PDF 14–15), Theorem 1 and Table 2

import Mathlib
import Definitions.Def_MultitierCSR_Strategy_Model

namespace MultitierCSR.Strategy

/-- Huang–Song–Swinney, Theorem 1, pp. 14–15 (PDF 14–15). -/
theorem theorem_1 (P : Params) (hS : P.Standing)
    (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1) :
    (∀ x0 : ℝ, IsBuyerOptimal P σ2 σ1 x0 → ¬ (0 < x0 ∧ 0 < σ1 x0)) ∧
    (P.tau1 < P.tau2 / P.b ^ 2 →
      (P.tau0 ≤ P.tau1 / 4 → ChoiceRow P σ2 σ1 (controlRow P)) ∧
      (P.tau1 / 4 < P.tau0 → P.tau0 ≤ P.tau1 →
        (P.tau2 ≤ g P → ChoiceRow P σ2 σ1 (controlRow P)) ∧
        (g P < P.tau2 → ChoiceRow P σ2 σ1 (delegationRow P))) ∧
      (P.tau1 < P.tau0 → ChoiceRow P σ2 σ1 (delegationRow P))) ∧
    (P.tau2 / P.b ^ 2 ≤ P.tau1 →
      (P.tau0 ≤ P.tau2 / P.b ^ 2 →
        ChoiceRow P σ2 σ1 (controlRow P)) ∧
      (P.tau2 / P.b ^ 2 < P.tau0 →
        ChoiceRow P σ2 σ1 (noEffortRow P))) := by sorry

end MultitierCSR.Strategy
