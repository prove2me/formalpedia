-- Prove2me | Theorems.Thm_MultitierCSR_Strategy_lemma_2
-- name    : MultitierCSR.Strategy.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:52.798704+00:00
-- url     : https://prove2.me/theorems/7639c5db-f446-460b-9e30-6991e0ba95f6
-- title:
--   Lemma 2, p. 13 — Tier 1's best response and violation probabilities
-- statement:
--   Fix any nonnegative buyer effort $x_0$, and let Tier 2 play a best response after each feasible history. Tier 1's resulting profit is concave in its own effort and has the unique maximizer
--
--   $$
--   x_1^*(x_0)=\bigl(\sqrt{\tau_2/\tau_1}-b-x_0\bigr)^+.
--   $$
--
--   If $x_0\le\sqrt{\tau_2/\tau_1}-b$, the actual and detected violation probabilities are $\sqrt{\tau_1\tau_2}/\beta$ and $\sqrt{\tau_1\tau_2}$. If $x_0>\sqrt{\tau_2/\tau_1}-b$, they are $\tau_2/[\beta(x_0+b)]$ and $\tau_2/(x_0+b)$. A Tier 1 best-response strategy exists.
--
--   This step supplies the buyer's induced risk as a function of its own effort.
-- source:
--   Huang, Song & Swinney, Managing Social Responsibility in Multitier Supply Chains, SSRN 2837332 (version of October 2021), p. 13 (PDF 13), Lemma 2; proof in Online Supplement p. 1 (PDF 34)

import Mathlib
import Definitions.Def_MultitierCSR_Strategy_Model

namespace MultitierCSR.Strategy

/-- Huang–Song–Swinney, Lemma 2, p. 13 (PDF 13). -/
theorem lemma_2 (P : Params) (hS : P.Standing)
    (σ2 : ℝ → ℝ → ℝ) (h2 : IsBestResponse2 P σ2) :
    (∀ x0 : ℝ, 0 ≤ x0 →
      let e := tier1Candidate P x0
      ConcaveOn ℝ (Set.Ici (0 : ℝ))
        (fun x1 => profit1 P x0 x1 (σ2 x0 x1)) ∧
      0 ≤ e ∧
      (∀ y : ℝ, 0 ≤ y →
        profit1 P x0 y (σ2 x0 y) ≤ profit1 P x0 e (σ2 x0 e)) ∧
      (∀ y : ℝ, 0 ≤ y →
        (∀ z : ℝ, 0 ≤ z →
          profit1 P x0 z (σ2 x0 z) ≤ profit1 P x0 y (σ2 x0 y)) → y = e) ∧
      (x0 ≤ Real.sqrt (P.tau2 / P.tau1) - P.b →
        violationProb P x0 e (σ2 x0 e) =
            Real.sqrt (P.tau1 * P.tau2) / P.β ∧
        detectedProb P x0 e (σ2 x0 e) =
            Real.sqrt (P.tau1 * P.tau2)) ∧
      (Real.sqrt (P.tau2 / P.tau1) - P.b < x0 →
        violationProb P x0 e (σ2 x0 e) =
            P.tau2 / (P.β * (x0 + P.b)) ∧
        detectedProb P x0 e (σ2 x0 e) = P.tau2 / (x0 + P.b))) ∧
    (∃ σ1 : ℝ → ℝ, IsBestResponse1 P σ2 σ1) := by sorry

end MultitierCSR.Strategy
