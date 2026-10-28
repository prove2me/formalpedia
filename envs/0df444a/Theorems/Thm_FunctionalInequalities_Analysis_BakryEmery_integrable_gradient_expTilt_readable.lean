-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_gradient_expTilt_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integrable_gradient_expTilt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:56.913856+00:00
-- url     : https://prove2.me/theorems/4ce78d47-f6fb-43d4-9cf4-e4a847a5b302
-- title:
--   Integrability of Compactly Supported Gradients Under Tilting
-- statement:
--   This theorem establishes integrability of the gradient of a compactly supported function under every exponential tilt.
--
--   Let $E$ be a finite-dimensional complete real inner-product space, let $m$ be a measure on $E$, and let $V,f:E\to\mathbb R$. If $f$ is $C^2$ and has compact support, then for every $z\in E$,
--
--   $$\nabla f\in L^1\!\left(\operatorname{expTilt}\bigl(m.\operatorname{tilted}(-V),z\bigr)\right).$$
--
--   No regularity or integrability hypothesis on $V$ is present in the type. This is a technical ingredient for integration by parts and tilt-average identities.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_gradient_expTilt {V f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
--       (z : E) : Integrable (gradient f) (expTilt (m.tilted (-V)) z)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Previous: [`expTilt_tilted`](https://prove2.me/theorems/b77ce921-0d7b-4b31-ac8b-28afb215f4d2) · Next: [`tiltAverage_neg_weightedLaplacian`](https://prove2.me/theorems/2049b0ee-2e67-44f2-a194-81ea5ae5e577).
--
--   [Source excerpt, lines 122–123](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean#L122-L123) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean#L119-L137 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.integrable_gradient_expTilt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic

open MeasureTheory FunctionalInequalities.Analysis.Tensor
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
omit [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integrable_gradient_expTilt_readable {V f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (z : E) : Integrable (gradient f) (expTilt (m.tilted (-V)) z) := by sorry
