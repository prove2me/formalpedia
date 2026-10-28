-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_hasDerivAt_weighted_integral_of_compact_readable
-- name    : FunctionalInequalities.Probability.Posterior.hasDerivAt_weighted_integral_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:59.436375+00:00
-- url     : https://prove2.me/theorems/54d90089-92ce-40ab-9311-3ac0348d33d5
-- title:
--   Derivative of a Weighted Tilted Integral
-- statement:
--   This is the compact-support differentiation lemma preceding the posterior expectation formula.
--
--   Let $\mu$ be a probability measure on a topological, measurable, second-countable Borel space $\Omega$, and assume its support is compact. Let $\phi,g:\Omega\to\mathbb R$ be continuous and let $f:\Omega\to\mathbb R$ be measurable. Assume that for some $C\ge0$,
--
--   $$\lVert f(x)\rVert\le C\quad\text{for every }x\in\operatorname{supp}\mu.$$
--
--   Then the map
--
--   $$t\longmapsto\int_\Omega e^{\phi(x)+t g(x)}f(x)\,d\mu(x)$$
--
--   has derivative at $t=0$ equal to
--
--   $$\int_\Omega e^{\phi(x)}g(x)f(x)\,d\mu(x).$$
--
--   This result supplies differentiation under the integral sign for unnormalized compactly supported tilts.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasDerivAt_weighted_integral_of_compact (μ : ProbabilityMeasure Ω)
--       (hc : IsCompact (μ : Measure Ω).support) {φ g f : Ω → ℝ}
--       (hφ : Continuous φ) (hg : Continuous g) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
--       (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
--       HasDerivAt (fun t : ℝ => ∫ x, Real.exp (φ x + t * g x) * f x ∂(μ : Measure Ω))
--         (∫ x, Real.exp (φ x) * g x * f x ∂(μ : Measure Ω)) 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/CompactPrior`](https://prove2.me/theorems/e9642070-1d94-4ba1-98bc-8d40d5fe9489).
--
--   Next: [`expectation_hasDerivAt_of_compact`](https://prove2.me/theorems/33fce4ba-fea7-459e-923c-b736676bd849).
--
--   [Source excerpt, lines 86–91](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L86-L91) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L85-L129 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactPrior`, declaration `FunctionalInequalities.Probability.Posterior.hasDerivAt_weighted_integral_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior

open MeasureTheory Filter Topology ProbabilityTheory
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]

theorem FunctionalInequalities.Probability.Posterior.hasDerivAt_weighted_integral_of_compact_readable (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ g f : Ω → ℝ}
    (hφ : Continuous φ) (hg : Continuous g) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (φ x + t * g x) * f x ∂(μ : Measure Ω))
      (∫ x, Real.exp (φ x) * g x * f x ∂(μ : Measure Ω)) 0 := by sorry
