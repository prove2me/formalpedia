-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Mollification_gradient_convolution_readable
-- name    : FunctionalInequalities.Analysis.Mollification.gradient_convolution_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:48.461181+00:00
-- url     : https://prove2.me/theorems/fe7a116d-bd27-498e-9e9e-354056906010
-- title:
--   Gradient Commutation with Mollification
-- statement:
--   This states that mollification commutes with the gradient for smooth compactly supported scalar functions.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, and let $\varphi$ be a smooth bump centered at $0$. If $g:V\to\mathbb{R}$ is smooth and compactly supported, then for every $x\in V$,
--
--   $$\nabla\bigl((\varphi_{\mathrm{normed}}\ast g)(x)\bigr)
--   =\bigl(\varphi_{\mathrm{normed}}\ast\nabla g\bigr)(x).$$
--
--   The gradient on the right is vector-valued, and the convolution uses the scalar multiplication continuous linear map. This identity is useful for transferring differential estimates through mollification.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Mollification`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gradient_convolution {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
--       (x : V) :
--       gradient (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x =
--         (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] gradient g) x
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Mollification/Basic`](https://prove2.me/theorems/b351487c-eaef-4d4f-b656-728d01c5702d).
--
--   Previous: [`integral_inner_convolution_eq`](https://prove2.me/theorems/fd3d77b4-2913-4723-a4fd-5a1404fbf923) · Next: [`laplacian_convolution`](https://prove2.me/theorems/0855ca87-12f0-432a-bb25-ce692eba493f).
--
--   [Source excerpt, lines 360–363](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L360-L363) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L358-L385 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.Mollification.gradient_convolution`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

open scoped Convolution ContDiff ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
variable (φ : ContDiffBump (0 : V))

theorem FunctionalInequalities.Analysis.Mollification.gradient_convolution_readable {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : V) :
    gradient (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x =
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] gradient g) x := by sorry
