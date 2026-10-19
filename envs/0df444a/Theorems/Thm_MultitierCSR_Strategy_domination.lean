-- Prove2me | Theorems.Thm_MultitierCSR_Strategy_domination
-- name    : MultitierCSR.Strategy.domination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:56.259984+00:00
-- url     : https://prove2.me/theorems/acd79dd7-ac65-493a-89ba-88fbcb84ed37
-- title:
--   §4.1, p. 14 — positive intermediate buyer effort is dominated by zero
-- statement:
--   Suppose $b<\sqrt{\tau_2/\tau_1}$ and both suppliers best respond. For every positive buyer effort up to and including the point where Tier 1 stops exerting effort,
--
--   $$
--   0<x_0\le\sqrt{\tau_2/\tau_1}-b
--   \quad\Longrightarrow\quad
--   \Pi_0(x_0)<\Pi_0(0).
--   $$
--
--   Thus a buyer that induces positive Tier 1 effort cannot improve its own payoff by also exerting positive effort in this range.
--
--   **Formalization Note** The prose claim includes $x_0\le\sqrt{\tau_2/\tau_1}-b$; the positive lower bound is required for strict domination, since zero cannot strictly dominate itself.
-- source:
--   Huang, Song & Swinney, Managing Social Responsibility in Multitier Supply Chains, SSRN 2837332 (version of October 2021), p. 14 (PDF 14), §4.1, paragraph beginning 'Lemma 2 implies'

import Mathlib
import Definitions.Def_MultitierCSR_Strategy_Model

namespace MultitierCSR.Strategy

/-- The strict domination claim of §4.1, p. 14 (PDF 14), for positive buyer effort. -/
theorem domination (P : Params) (hS : P.Standing)
    (σ2 : ℝ → ℝ → ℝ) (σ1 : ℝ → ℝ)
    (h2 : IsBestResponse2 P σ2) (h1 : IsBestResponse1 P σ2 σ1)
    (hb : P.b < Real.sqrt (P.tau2 / P.tau1)) :
    ∀ x0 : ℝ, 0 < x0 → x0 ≤ Real.sqrt (P.tau2 / P.tau1) - P.b →
      buyerProfit P σ2 σ1 x0 < buyerProfit P σ2 σ1 0 := by sorry

end MultitierCSR.Strategy
