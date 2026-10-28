-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Mollification_laplacian_convolution_readable
-- name    : FunctionalInequalities.Analysis.Mollification.laplacian_convolution_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:46.995847+00:00
-- url     : https://prove2.me/theorems/0855ca87-12f0-432a-bb25-ce692eba493f
-- title:
--   Laplacian Commutation with Mollification
-- statement:
--   This states that mollification commutes with the Laplacian for smooth compactly supported scalar functions.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, and let $\varphi$ be a smooth bump centered at $0$. If $g:V\to\mathbb{R}$ is smooth and compactly supported, then for every $x\in V$,
--
--   $$\Delta\bigl((\varphi_{\mathrm{normed}}\ast g)(x)\bigr)
--   =\bigl(\varphi_{\mathrm{normed}}\ast\Delta g\bigr)(x).$$
--
--   Here $\Delta$ is `Laplacian.laplacian`. This provides the second-order analogue of the gradient commutation identity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Mollification`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem laplacian_convolution {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
--       (x : V) :
--       Laplacian.laplacian (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x =
--         (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] Laplacian.laplacian g) x
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Mollification/Basic`](https://prove2.me/theorems/b351487c-eaef-4d4f-b656-728d01c5702d).
--
--   Previous: [`gradient_convolution`](https://prove2.me/theorems/fe7a116d-bd27-498e-9e9e-354056906010) · Next: [`integral_fderiv_kernel_eq`](https://prove2.me/theorems/8b5ca05b-ad73-4f24-8770-85db445dfaf1).
--
--   [Source excerpt, lines 389–392](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L389-L392) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L387-L435 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.Mollification.laplacian_convolution`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

open scoped Convolution ContDiff ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
variable (φ : ContDiffBump (0 : V))

theorem FunctionalInequalities.Analysis.Mollification.laplacian_convolution_readable {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : V) :
    Laplacian.laplacian (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x =
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] Laplacian.laplacian g) x := by sorry
