-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_covariance_hasDerivAt_of_compact_readable
-- name    : FunctionalInequalities.Probability.Posterior.covariance_hasDerivAt_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:02.787389+00:00
-- url     : https://prove2.me/theorems/9b3908cf-2697-4638-b0df-be6209e77920
-- title:
--   Derivative of a Tilted Covariance
-- statement:
--   This is the compact-support derivative formula for a tilted covariance.
--
--   Let $\mu$ be a compactly supported probability measure on a topological, measurable, second-countable Borel space. Let $\phi,g,k$ be continuous and let $f$ be measurable and bounded on $\operatorname{supp}\mu$ by some $C\ge0$. Then
--
--   $$\left.\frac{d}{dt}\right|_{t=0}\operatorname{Cov}_{\mu.\operatorname{tilted}(\phi+t g)}(f,k)
--   =\operatorname{Cov}_{\mu.\operatorname{tilted}(\phi)}(f,gk)
--   -\left(\int g\,d\nu\right)\operatorname{Cov}_{\nu}(f,k)
--   -\left(\int k\,d\nu\right)\operatorname{Cov}_{\nu}(f,g),$$
--
--   where $\nu=\mu.\operatorname{tilted}(\phi)$. This provides the covariance derivative needed for second-order posterior calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem covariance_hasDerivAt_of_compact (μ : ProbabilityMeasure Ω)
--       (hc : IsCompact (μ : Measure Ω).support) {φ g k f : Ω → ℝ}
--       (hφ : Continuous φ) (hg : Continuous g) (hk : Continuous k) (hf : Measurable f)
--       {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
--       HasDerivAt (fun t : ℝ => covariance f k
--         ((μ : Measure Ω).tilted (fun x => φ x + t * g x)))
--         (covariance f (fun x => g x * k x) ((μ : Measure Ω).tilted φ) -
--           (∫ x, g x ∂((μ : Measure Ω).tilted φ)) * covariance f k ((μ : Measure Ω).tilted φ) -
--           (∫ x, k x ∂((μ : Measure Ω).tilted φ)) * covariance f g ((μ : Measure Ω).tilted φ)) 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/CompactPrior`](https://prove2.me/theorems/e9642070-1d94-4ba1-98bc-8d40d5fe9489).
--
--   Supporting theorems: [`expectation_hasDerivAt_of_compact`](https://prove2.me/theorems/33fce4ba-fea7-459e-923c-b736676bd849).
--
--   Previous: [`norm_integral_tilted_le_of_compact`](https://prove2.me/theorems/ae0bd956-6f80-4999-b550-1b58967f1160).
--
--   [Source excerpt, lines 205–213](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L205-L213) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean#L202-L260 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactPrior`, declaration `FunctionalInequalities.Probability.Posterior.covariance_hasDerivAt_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactPrior

open MeasureTheory Filter Topology ProbabilityTheory
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [SecondCountableTopology Ω]

theorem FunctionalInequalities.Probability.Posterior.covariance_hasDerivAt_of_compact_readable (μ : ProbabilityMeasure Ω)
    (hc : IsCompact (μ : Measure Ω).support) {φ g k f : Ω → ℝ}
    (hφ : Continuous φ) (hg : Continuous g) (hk : Continuous k) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure Ω).support, ‖f x‖ ≤ C) :
    HasDerivAt (fun t : ℝ => covariance f k
      ((μ : Measure Ω).tilted (fun x => φ x + t * g x)))
      (covariance f (fun x => g x * k x) ((μ : Measure Ω).tilted φ) -
        (∫ x, g x ∂((μ : Measure Ω).tilted φ)) * covariance f k ((μ : Measure Ω).tilted φ) -
        (∫ x, k x ∂((μ : Measure Ω).tilted φ)) * covariance f g ((μ : Measure Ω).tilted φ)) 0 := by sorry
