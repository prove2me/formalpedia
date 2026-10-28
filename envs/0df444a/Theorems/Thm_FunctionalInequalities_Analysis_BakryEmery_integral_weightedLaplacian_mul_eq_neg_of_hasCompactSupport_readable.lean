-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:09.332089+00:00
-- url     : https://prove2.me/theorems/7f163639-82cc-4c30-a575-6b63cecd216c
-- title:
--   Compactly Supported Integration by Parts
-- statement:
--   This is the compactly supported integration-by-parts identity for the weighted Laplacian.
--
--   Let $E$ be finite-dimensional, complete, and equipped with a real inner product; let $m$ be an additive Haar measure; and let $V,f,w:E\to\mathbb R$. Assume that $V$ is $C^1$, $f$ and $w$ are $C^2$, and $w$ has compact support. Then
--
--   $$\int (\mathcal L_Vf)(x)w(x)\,d\bigl(m.\operatorname{tilted}(-V)\bigr)(x)
--   =-\int\langle\nabla f(x),\nabla w(x)\rangle\,d\bigl(m.\operatorname{tilted}(-V)\bigr)(x).$$
--
--   Here `weightedLaplacian V f` is $\mathcal L_Vf$. The result is the compact-support form of the first integration-by-parts equality.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport {V f w : E → ℝ}
--       (hV : ContDiff ℝ 1 V) (hf : ContDiff ℝ 2 f) (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) :
--       ∫ x, weightedLaplacian V f x * w x ∂(m.tilted (-V)) =
--         -∫ x, ⟪gradient f x, gradient w x⟫ ∂(m.tilted (-V))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/Temperate`](https://prove2.me/theorems/64f88da4-493d-4b67-b32e-a328cef27c70).
--
--   Definition modules: [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Supporting theorems: [`cutoff_eq_one`](https://prove2.me/theorems/85395b56-b174-481f-86b1-0d68ab4624ec), [`hasCompactSupport_cutoff`](https://prove2.me/theorems/d329d169-7e19-4110-aeb8-20df20dddcfb).
--
--   Next: [`integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth`](https://prove2.me/theorems/4b2c3c7b-c447-49e8-8a0e-99319495a94d).
--
--   [Source excerpt, lines 27–30](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/Temperate.lean#L27-L30) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/Temperate.lean#L25-L117 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Temperate

open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport_readable {V f w : E → ℝ}
    (hV : ContDiff ℝ 1 V) (hf : ContDiff ℝ 2 f) (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) :
    ∫ x, weightedLaplacian V f x * w x ∂(m.tilted (-V)) =
      -∫ x, ⟪gradient f x, gradient w x⟫ ∂(m.tilted (-V)) := by sorry
