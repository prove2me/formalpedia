-- Prove2me | Theorems.Thm_MultitierCSR_Strategy_lemma_1
-- name    : MultitierCSR.Strategy.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:55.179686+00:00
-- url     : https://prove2.me/theorems/e04bc4e8-05f8-4d44-8ce2-0175d71aeea9
-- title:
--   Lemma 1, p. 12 — Tier 2's best response and violation probabilities
-- statement:
--   Fix any nonnegative efforts $x_0,x_1$ from Tiers 0 and 1. Under the model's standing assumptions, Tier 2's profit is concave in its own nonnegative effort and has a unique maximizer:
--
--   $$
--   x_2^*(x_0,x_1)=\frac{\ln[\beta(x_0+x_1+b)/\tau_2]}{x_0+x_1+b},\quad
--   \lambda^*(x_0,x_1)=\frac{\tau_2}{\beta(x_0+x_1+b)},\quad
--   \alpha^*(x_0,x_1)=\frac{\tau_2}{x_0+x_1+b}.
--   $$
--
--   A Tier 2 best-response strategy exists for all feasible histories. The lemma supplies the first step of backward induction without defining optimality by this formula.
-- source:
--   Huang, Song & Swinney, Managing Social Responsibility in Multitier Supply Chains, SSRN 2837332 (version of October 2021), p. 12 (PDF 12), Lemma 1; proof in Online Supplement p. 1 (PDF 34)

import Mathlib
import Definitions.Def_MultitierCSR_Strategy_Model

namespace MultitierCSR.Strategy

/-- Huang–Song–Swinney, Lemma 1, p. 12 (PDF 12). -/
theorem lemma_1 (P : Params) (hS : P.Standing) :
    (∀ x0 x1 : ℝ, 0 ≤ x0 → 0 ≤ x1 →
      let e := tier2Candidate P x0 x1
      ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun x2 => profit2 P x0 x1 x2) ∧
      0 ≤ e ∧
      (∀ y : ℝ, 0 ≤ y → profit2 P x0 x1 y ≤ profit2 P x0 x1 e) ∧
      (∀ y : ℝ, 0 ≤ y →
        (∀ z : ℝ, 0 ≤ z → profit2 P x0 x1 z ≤ profit2 P x0 x1 y) → y = e) ∧
      violationProb P x0 x1 e = P.tau2 / (P.β * (x0 + x1 + P.b)) ∧
      detectedProb P x0 x1 e = P.tau2 / (x0 + x1 + P.b)) ∧
    (∃ σ2 : ℝ → ℝ → ℝ, IsBestResponse2 P σ2) := by sorry

end MultitierCSR.Strategy
