-- Prove2me | Theorems.Thm_MultitierCSR_Strategy_control_delegation_comparison
-- name    : MultitierCSR.Strategy.control_delegation_comparison
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:05.569674+00:00
-- url     : https://prove2.me/theorems/74a13761-6d2c-4722-9ec7-90887815a9a3
-- title:
--   Proof of Theorem 1, Supplement p. 1 — control versus delegation
-- statement:
--   Suppose Tier 1's loss-adjusted effort cost is low, $\tau_1<\tau_2/b^2$, and $\tau_0\le\tau_1$. With both suppliers best responding, the buyer's payoff from delegation, at $x_0=0$, is strictly below its payoff at the control candidate $x_0=\sqrt{\tau_2/\tau_0}-b$ exactly when
--
--   $$
--   b\tau_0-2\sqrt{\tau_0\tau_2}+\sqrt{\tau_1\tau_2}>0.
--   $$
--
--   This is the comparison used to identify the control–delegation threshold in Theorem 1.
-- source:
--   Huang, Song & Swinney, Managing Social Responsibility in Multitier Supply Chains, SSRN 2837332 (version of October 2021), Online Supplement p. 1 (PDF 34), proof of Theorem 1, control versus delegation displays

import Mathlib
import Definitions.Def_MultitierCSR_Strategy_Model

namespace MultitierCSR.Strategy

/-- Comparison in the proof of Theorem 1, Online Supplement p. 1 (PDF 34). -/
theorem control_delegation_comparison (P : Params) (hS : P.Standing)
    (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1)
    (hCheap : P.tau1 < P.tau2 / P.b ^ 2)
    (hCost : P.tau0 ≤ P.tau1) :
    (buyerProfit P σ2 σ1 0 <
      buyerProfit P σ2 σ1 (Real.sqrt (P.tau2 / P.tau0) - P.b)) ↔
    0 < P.b * P.tau0 - 2 * Real.sqrt (P.tau0 * P.tau2) +
      Real.sqrt (P.tau1 * P.tau2) := by sorry

end MultitierCSR.Strategy
