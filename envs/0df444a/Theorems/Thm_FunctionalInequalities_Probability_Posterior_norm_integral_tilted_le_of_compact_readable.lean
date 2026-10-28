-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_norm_integral_tilted_le_of_compact_readable
-- name    : FunctionalInequalities.Probability.Posterior.norm_integral_tilted_le_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:47.620009+00:00
-- url     : https://prove2.me/theorems/ae0bd956-6f80-4999-b550-1b58967f1160
-- title:
--   Support-Bound Preservation Under Exponential Tilting
-- statement:
--   This statement formalizes the support-bound estimate for tilted expectations in the compact-prior stage of Bizeul–Klartag–Lehec, p. 19.
--
--   Let $\Omega$ be a topological, measurable, Borel, second-countable space, and let $\mu$ be a probability measure with compact support. Let $\varphi:\Omega\to\mathbb R$ be continuous and let $f:\Omega\to\mathbb R$ be measurable. Suppose $C\in\mathbb R$ satisfies $0\leq C$ and
--
--   $$
--   \|f(x)\|\leq C
--   $$
--
--   on the support of $\mu$. Then the integral of $f$ against the exponentially tilted measure is bounded by the same constant:
--
--   $$
--   \left\|\int f\,d(\mu.\operatorname{tilted}\varphi)\right\|\leq C.
--   $$
--
--   This is a finite-valued norm estimate for a tilted probability expectation and is useful for controlling posterior statistics.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_integral_tilted_le_of_compact (μ : ProbabilityMeasure Ω)
--       (hc : IsCompact (μ : Measure Ω).support) {φ f : Ω → ℝ}
--       (hφ : Continuous φ) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
--       (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
--       ‖∫ x, f x ∂((μ : Measure Ω).tilted φ)‖ ≤ C
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/CompactPrior`](https://prove2.me/theorems/e9642070-1d94-4ba1-98bc-8d40d5fe9489).
--
--   Previous: [`expectation_hasDerivAt_of_compact`](https://prove2.me/theorems/33fce4ba-fea7-459e-923c-b736676bd849) · Next: [`covariance_hasDerivAt_of_compact`](https://prove2.me/theorems/9b3908cf-2697-4638-b0df-be6209e77920).
--
--   [Source excerpt, lines 174–178](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L174-L178) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L173-L191 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactPrior`, declaration `FunctionalInequalities.Probability.Posterior.norm_integral_tilted_le_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior

open MeasureTheory Filter Topology ProbabilityTheory
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]

theorem FunctionalInequalities.Probability.Posterior.norm_integral_tilted_le_of_compact_readable (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ f : Ω → ℝ}
    (hφ : Continuous φ) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    ‖∫ x, f x ∂((μ : Measure Ω).tilted φ)‖ ≤ C := by sorry
