-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_integrable_exp_norm_mul_of_compact_readable
-- name    : FunctionalInequalities.Probability.Posterior.integrable_exp_norm_mul_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:53.002658+00:00
-- url     : https://prove2.me/theorems/93df8d91-b0d9-4aa8-a712-e52703fff899
-- title:
--   Exponential-Norm Integrability Under a Compact Prior
-- statement:
--   This statement formalizes an integrability estimate for compactly supported posterior weights.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\mu$ be a probability measure on $E$ whose measure-theoretic support is compact. Let $f:E\to\mathbb R$ be measurable. Let $C\in\mathbb R$ satisfy $0\leq C$, and assume
--
--   $$
--   \|f(x)\|\leq C
--   $$
--
--   for every $x$ in the support of $\mu$. For any continuous linear map $Q:E\to E$ and any $s\in\mathbb R$, the function
--
--   $$
--   x\mapsto e^{s\|x\|}\left\|e^{E_{0,Q}(x)}f(x)\right\|
--   $$
--
--   is integrable with respect to $\mu$, where `quadraticExponent 0 Q x` is $E_{0,Q}(x)$:
--
--   $$
--   \int e^{s\|x\|}\left\|e^{E_{0,Q}(x)}f(x)\right\|\,d\mu(x)<\infty.
--   $$
--
--   This compact-support estimate supplies the domination needed for smooth parameter differentiation of posterior integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_exp_norm_mul_of_compact (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
--       {C : ℝ} (_hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
--       (Q : E →L[ℝ] E) (s : ℝ) :
--       Integrable (fun x => Real.exp (s * ‖x‖) * ‖Real.exp (quadraticExponent 0 Q x) * f x‖) (μ : Measure E)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363).
--
--   Definition modules: [`Probability/Posterior/Exponent`](https://prove2.me/theorems/36c30d18-f69a-4499-bf5e-0d0678b5706c).
--
--   Next: [`contDiff_weighted_integral_quadraticExponent_of_compact`](https://prove2.me/theorems/4fe89257-70b6-4433-b7b3-1b2d874f4eb1).
--
--   [Source excerpt, lines 34–38](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L34-L38) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Generator.lean#L33-L58 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Generator`, declaration `FunctionalInequalities.Probability.Posterior.integrable_exp_norm_mul_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator

open MeasureTheory Filter Topology ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.Posterior.integrable_exp_norm_mul_of_compact_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) {f : E → ℝ} (hf : Measurable f)
    {C : ℝ} (_hC : 0 ≤ C) (hfb : ∀ x ∈ (μ : Measure E).support, ‖f x‖ ≤ C)
    (Q : E →L[ℝ] E) (s : ℝ) :
    Integrable (fun x => Real.exp (s * ‖x‖) * ‖Real.exp (quadraticExponent 0 Q x) * f x‖) (μ : Measure E) := by sorry
