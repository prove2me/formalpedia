-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:07.137798+00:00
-- url     : https://prove2.me/theorems/4b2c3c7b-c447-49e8-8a0e-99319495a94d
-- title:
--   Integration by Parts for Temperate-Growth Functions
-- statement:
--   Let $E$ be finite-dimensional and complete with a real inner product, let $m$ be an additive Haar measure, and let $V,f,g:E\to\mathbb R$. Assume:
--
--   1. $V$ is $C^1$.
--   2. $\|\nabla V(x)\|\le C_V(1+\|x\|)^{k_V}$ for some $C_V\in\mathbb R$ and $k_V\in\mathbb N$.
--   3. Every exponential moment is integrable for $m.\operatorname{tilted}(-V)$.
--   4. $f$ and $g$ have `HasTemperateGrowth`.
--
--   Then
--
--   $$\int (\mathcal L_Vf)g\,d\mu=-\int\langle\nabla f,\nabla g\rangle\,d\mu,
--   \qquad \mu=m.\operatorname{tilted}(-V).$$
--
--   This is the first equality in the temperate-growth integration-by-parts formula and is reusable for weighted diffusion identities.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth {V f g : E → ℝ}
--       (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
--       (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
--       ∫ x, weightedLaplacian V f x * g x ∂(m.tilted (-V)) =
--         -∫ x, ⟪gradient f x, gradient g x⟫ ∂(m.tilted (-V))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/Temperate`](https://prove2.me/theorems/64f88da4-493d-4b67-b32e-a328cef27c70).
--
--   Definition modules: [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Selected supporting theorems: [`abs_laplacian_le`](https://prove2.me/theorems/f6e58a8e-3f46-421d-a064-a1f1705fd429), [`cutoff_eq_one`](https://prove2.me/theorems/85395b56-b174-481f-86b1-0d68ab4624ec), [`hasCompactSupport_cutoff`](https://prove2.me/theorems/d329d169-7e19-4110-aeb8-20df20dddcfb), [`integrable_of_norm_le_pow`](https://prove2.me/theorems/7386231a-1383-4b09-86a5-2387ba9cd6db), [`integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport`](https://prove2.me/theorems/7f163639-82cc-4c30-a575-6b63cecd216c).
--
--   Previous: [`integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport`](https://prove2.me/theorems/7f163639-82cc-4c30-a575-6b63cecd216c).
--
--   [Source excerpt, lines 162–167](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/Temperate.lean#L162-L167) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Equation (15) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), cited as Equation (15), p. 6.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (15), p. 6 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/Temperate.lean#L161-L287 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Temperate

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth_readable {V f g : E → ℝ}
    (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    ∫ x, weightedLaplacian V f x * g x ∂(m.tilted (-V)) =
      -∫ x, ⟪gradient f x, gradient g x⟫ ∂(m.tilted (-V)) := by sorry
