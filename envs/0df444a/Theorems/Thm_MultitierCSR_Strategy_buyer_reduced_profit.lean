-- Prove2me | Theorems.Thm_MultitierCSR_Strategy_buyer_reduced_profit
-- name    : MultitierCSR.Strategy.buyer_reduced_profit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:57.699993+00:00
-- url     : https://prove2.me/theorems/34cad8fc-06d3-4d90-a02c-a0eba5d8b24d
-- title:
--   Proof of Theorem 1, Supplement p. 1 — buyer's piecewise reduced profit
-- statement:
--   After both suppliers best respond, the buyer's profit as a function of its nonnegative effort $x_0$ is
--
--   $$
--   \Pi_0(x_0)=\begin{cases}
--   m_0d-k_0x_0-\sqrt{\tau_1\tau_2}\,\ell_0,&0\le x_0\le\sqrt{\tau_2/\tau_1}-b,\\
--   m_0d-k_0x_0-\ell_0\tau_2/(x_0+b),&x_0>\sqrt{\tau_2/\tau_1}-b.
--   \end{cases}
--   $$
--
--   The first interval can be empty; then the second formula applies to every feasible buyer effort. This identity is the profit function used in the proof of Theorem 1.
-- source:
--   Huang, Song & Swinney, Managing Social Responsibility in Multitier Supply Chains, SSRN 2837332 (version of October 2021), Online Supplement p. 1 (PDF 34), proof of Theorem 1, piecewise display

import Mathlib
import Definitions.Def_MultitierCSR_Strategy_Model

namespace MultitierCSR.Strategy

/-- Proof of Theorem 1, Online Supplement p. 1 (PDF 34). -/
theorem buyer_reduced_profit (P : Params) (hS : P.Standing)
    (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1) :
    ∀ x0 : ℝ, 0 ≤ x0 →
      (x0 ≤ Real.sqrt (P.tau2 / P.tau1) - P.b →
        buyerProfit P σ2 σ1 x0 =
          P.m0 * P.d - P.k0 * x0 - Real.sqrt (P.tau1 * P.tau2) * P.ell0) ∧
      (Real.sqrt (P.tau2 / P.tau1) - P.b < x0 →
        buyerProfit P σ2 σ1 x0 =
          P.m0 * P.d - P.k0 * x0 - P.ell0 * P.tau2 / (x0 + P.b)) := by sorry

end MultitierCSR.Strategy
