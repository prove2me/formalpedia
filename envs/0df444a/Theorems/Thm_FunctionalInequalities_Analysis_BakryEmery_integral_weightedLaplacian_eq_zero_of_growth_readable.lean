-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_eq_zero_of_growth_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_eq_zero_of_growth_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:06.720568+00:00
-- url     : https://prove2.me/theorems/43e73809-b964-4849-8ee0-2937a72e6eac
-- title:
--   Vanishing Integral of the Weighted Laplacian
-- statement:
--   This theorem states the generator identity for a function with polynomial growth.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, and let $V,f:E\to\mathbb R$. Assume:
--
--   1. $V$ is $C^1$.
--   2. There are $C_V\in\mathbb R$ and $k_V\in\mathbb N$ such that $\|\nabla V(x)\|\le C_V(1+\|x\|)^{k_V}$.
--   3. Every exponential moment is integrable with respect to $m.\operatorname{tilted}(-V)$.
--   4. $f$ is $C^2$ and, for some $C\in\mathbb R$ and $k\in\mathbb N$, the functions $f$, $D f$, and $D^2f$ all have norm bounded by $C(1+\|x\|)^k$ pointwise, with the value bound stated using $|f(x)|$.
--
--   Then, writing $\mathcal L=\operatorname{weightedLaplacian}(V,\cdot)$,
--
--   $$\int \mathcal Lf\,d\bigl(m.\operatorname{tilted}(-V)\bigr)=0.$$
--
--   This is the polynomial-growth version of the weighted generator identity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_weightedLaplacian_eq_zero_of_growth {V f : E → ℝ} (hV : ContDiff ℝ 1 V)
--       {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
--       (hf : ContDiff ℝ 2 f) {C : ℝ} {k : ℕ}
--       (hfg : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ k ∧ ‖iteratedFDeriv ℝ 1 f x‖ ≤ C * (1 + ‖x‖) ^ k ∧
--         ‖iteratedFDeriv ℝ 2 f x‖ ≤ C * (1 + ‖x‖) ^ k) :
--       ∫ x, weightedLaplacian V f x ∂(m.tilted (-V)) = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/Temperate`](https://prove2.me/theorems/2dcac3f7-3919-472b-8b13-591e955577ca).
--
--   Definition modules: [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Selected supporting theorems: [`abs_laplacian_le`](https://prove2.me/theorems/f6e58a8e-3f46-421d-a064-a1f1705fd429), [`cutoff_eq_one`](https://prove2.me/theorems/85395b56-b174-481f-86b1-0d68ab4624ec), [`hasCompactSupport_cutoff`](https://prove2.me/theorems/d329d169-7e19-4110-aeb8-20df20dddcfb), [`integrable_of_norm_le_pow`](https://prove2.me/theorems/7386231a-1383-4b09-86a5-2387ba9cd6db), [`laplacian_mul`](https://prove2.me/theorems/8f824324-1746-4ab8-ac22-419276d90dc5).
--
--   Previous: [`integrable_of_norm_le_pow`](https://prove2.me/theorems/7386231a-1383-4b09-86a5-2387ba9cd6db).
--
--   [Source excerpt, lines 357–363](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L357-L363) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L355-L476 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_eq_zero_of_growth`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_eq_zero_of_growth_readable {V f : E → ℝ} (hV : ContDiff ℝ 1 V)
    {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : ContDiff ℝ 2 f) {C : ℝ} {k : ℕ}
    (hfg : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ k ∧ ‖iteratedFDeriv ℝ 1 f x‖ ≤ C * (1 + ‖x‖) ^ k ∧
      ‖iteratedFDeriv ℝ 2 f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    ∫ x, weightedLaplacian V f x ∂(m.tilted (-V)) = 0 := by sorry
