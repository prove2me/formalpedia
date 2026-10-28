-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_gradient_convolution_normed_readable
-- name    : FunctionalInequalities.Analysis.gradient_convolution_normed_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:04.66482+00:00
-- url     : https://prove2.me/theorems/1a83f340-6b76-45bf-8d07-2b59bc9e7ab0
-- title:
--   Gradient of a Mollified Scalar Function
-- statement:
--   This lemma identifies the gradient of a mollified scalar function.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel structure. Let $U:E\to\mathbb R$ be $C^1$ and suppose that $\nabla U$ is Lipschitz with constant $G\in[0,\infty)$. For every smooth compactly supported bump $\varphi$,
--
--   $$
--   \nabla\bigl(\varphi^{\mathrm{norm}}\!\ast U\bigr)
--   =
--   \varphi^{\mathrm{norm}}\!\ast\nabla U.
--   $$
--
--   The convolution is with respect to volume measure and scalar multiplication is represented by `ContinuousLinearMap.lsmul`. This technical identity supports approximation by smooth convolutions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma gradient_convolution_normed
--       {U : E → ℝ} (hU : ContDiff ℝ 1 U)
--       {G : NNReal} (hG : LipschitzWith G (gradient U))
--       (φ : ContDiffBump (0 : E)) :
--       gradient
--           (convolution
--             (φ.normed (volume : Measure E)) U
--             (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E)) =
--         convolution
--           (φ.normed (volume : Measure E)) (gradient U)
--           (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Mollification/Hessian`](https://prove2.me/theorems/3226f506-ca93-41c2-b914-cd900f4c6a41).
--
--   Next: [`exists_contDiff_approx_of_lipschitz_gradient`](https://prove2.me/theorems/58f49398-895c-40bc-ab6b-62bb53052379).
--
--   [Source excerpt, lines 85–95](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Mollification/Hessian.lean#L85-L95) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Hessian.lean#L85-L266 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Hessian`, declaration `_private.FunctionalInequalities.Analysis.Mollification.Hessian.0.FunctionalInequalities.Analysis.gradient_convolution_normed`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Hessian

open MeasureTheory Filter
variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma FunctionalInequalities.Analysis.gradient_convolution_normed_readable
    {U : E → ℝ} (hU : ContDiff ℝ 1 U)
    {G : NNReal} (hG : LipschitzWith G (gradient U))
    (φ : ContDiffBump (0 : E)) :
    gradient
        (convolution
          (φ.normed (volume : Measure E)) U
          (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E)) =
      convolution
        (φ.normed (volume : Measure E)) (gradient U)
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure E) := by sorry
