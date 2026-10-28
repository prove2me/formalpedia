-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Posterior_exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_readable
-- name    : FunctionalInequalities.Probability.Posterior.exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:49.780446+00:00
-- url     : https://prove2.me/theorems/840d9ee9-637c-4b2c-918e-01a3cf6f78a7
-- title:
--   Uniform Posterior Bounds for All Norm Moments
-- statement:
--   This statement formalizes a uniform moment bound in the compact-prior stage associated with Equation (67), p. 19, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\mu$ be a probability measure with compact support. Then there exists a radius $R\in\mathbb R$ such that $0\leq R$ and, for every $c\in E$, every continuous linear map $Q:E\to E$, and every $p\in\mathbb N$, the posterior associated with `quadraticExponent c Q` satisfies
--
--   1. $x\mapsto\|x\|^p$ is integrable under the tilted measure;
--   2. its moment is bounded by $R^p$:
--
--   $$
--   \int_E \|x\|^p\,d\mu_{c,Q}(x)\leq R^p.
--   $$
--
--   The same support radius works uniformly for all finite parameters $(c,Q)$ and all natural exponents $p$. The conclusion is an existence statement for $R$, not a claim that a particular displayed radius is chosen.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Posterior`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_uniform_norm_moments_tilted_quadraticExponent_of_compact (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) :
--       ∃ R : ℝ, 0 ≤ R ∧ ∀ (c : E) (Q : E →L[ℝ] E) (p : ℕ),
--         Integrable (fun x => ‖x‖ ^ p) ((μ : Measure E).tilted (quadraticExponent c Q)) ∧
--         (∫ x, ‖x‖ ^ p ∂((μ : Measure E).tilted (quadraticExponent c Q))) ≤ R ^ p
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Posterior/CompactQuadratic`](https://prove2.me/theorems/5018405c-ce78-4ccb-b2c7-5abb1f0295c8).
--
--   Definition modules: [`Probability/Posterior/Exponent`](https://prove2.me/theorems/36c30d18-f69a-4499-bf5e-0d0678b5706c).
--
--   Supporting theorems: [`norm_integral_tilted_le_of_compact`](https://prove2.me/theorems/ae0bd956-6f80-4999-b550-1b58967f1160).
--
--   [Source excerpt, lines 60–64](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/CompactQuadratic.lean#L60-L64) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/CompactQuadratic.lean#L58-L84 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.CompactQuadratic`, declaration `FunctionalInequalities.Probability.Posterior.exists_uniform_norm_moments_tilted_quadraticExponent_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactQuadratic

open MeasureTheory Filter Topology ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem FunctionalInequalities.Probability.Posterior.exists_uniform_norm_moments_tilted_quadraticExponent_of_compact_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (c : E) (Q : E →L[ℝ] E) (p : ℕ),
      Integrable (fun x => ‖x‖ ^ p) ((μ : Measure E).tilted (quadraticExponent c Q)) ∧
      (∫ x, ‖x‖ ^ p ∂((μ : Measure E).tilted (quadraticExponent c Q))) ≤ R ^ p := by sorry
