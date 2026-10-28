-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_expectation_hasDerivAt_of_compact_readable
-- name    : FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:12:58.970849+00:00
-- url     : https://prove2.me/theorems/33fce4ba-fea7-459e-923c-b736676bd849
-- title:
--   First Variation of a Compact Tilted Expectation
-- statement:
--   This formalizes the compact-prior first-variation statement related to Equation (67) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Equation (67), p. 19.
--
--   Let $\mu$ be a probability measure on a topological, measurable, second-countable Borel space with compact support. Let $\phi,g$ be continuous and let $f$ be measurable. Assume that for some $C\ge0$, $\lVert f(x)\rVert\le C$ on $\operatorname{supp}\mu$. For the tilted probability measure with exponent $\phi+t g$, the expectation satisfies
--
--   $$\left.\frac{d}{dt}\right|_{t=0}\int f\,d\bigl(\mu.\operatorname{tilted}(\phi+t g)\bigr)
--   =\operatorname{Cov}_{\mu.\operatorname{tilted}(\phi)}(f,g).$$
--
--   The notation `Measure.tilted` denotes the normalized exponential tilt. This lemma is the basic first-variation formula for compact posterior measures.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem expectation_hasDerivAt_of_compact (μ : ProbabilityMeasure Ω)
--       (hc : IsCompact (μ : Measure Ω).support) {φ g f : Ω → ℝ}
--       (hφ : Continuous φ) (hg : Continuous g) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
--       (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
--       HasDerivAt (fun t : ℝ => ∫ x, f x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x)))
--         (covariance f g ((μ : Measure Ω).tilted φ)) 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/CompactPrior`](https://prove2.me/theorems/e9642070-1d94-4ba1-98bc-8d40d5fe9489).
--
--   Supporting theorems: [`hasDerivAt_weighted_integral_of_compact`](https://prove2.me/theorems/54d90089-92ce-40ab-9311-3ac0348d33d5).
--
--   Previous: [`hasDerivAt_weighted_integral_of_compact`](https://prove2.me/theorems/54d90089-92ce-40ab-9311-3ac0348d33d5) · Next: [`norm_integral_tilted_le_of_compact`](https://prove2.me/theorems/ae0bd956-6f80-4999-b550-1b58967f1160).
--
--   [Source excerpt, lines 134–139](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L134-L139) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L131-L171 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactPrior`, declaration `FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior

open MeasureTheory Filter Topology ProbabilityTheory
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]

theorem FunctionalInequalities.Probability.Posterior.expectation_hasDerivAt_of_compact_readable (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ g f : Ω → ℝ}
    (hφ : Continuous φ) (hg : Continuous g) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => ∫ x, f x ∂((μ : Measure Ω).tilted (fun x => φ x + t * g x)))
      (covariance f g ((μ : Measure Ω).tilted φ)) 0 := by sorry
