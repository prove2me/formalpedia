-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_fderiv_convolution_eq_of_hasWeakDerivAlong_readable
-- name    : FunctionalInequalities.Analysis.fderiv_convolution_eq_of_hasWeakDerivAlong_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:55.454314+00:00
-- url     : https://prove2.me/theorems/21b92288-9077-4db1-9b99-ee62a25b6a04
-- title:
--   Mollification Commutes with Weak Directional Differentiation
-- statement:
--   This is the generic weak-derivative identity for mollification.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $f,g:E\to\mathbb{R}$ and $v\in E$, and assume `HasWeakDerivAlong f g v`. Let $\varphi$ be a smooth compactly supported bump centered at $0$, and let $x\in E$. Then
--
--   $$D_v\bigl((\varphi_{\mathrm{normed}}\ast f)(x)\bigr)
--   =(\varphi_{\mathrm{normed}}\ast g)(x).$$
--
--   In Lean, the directional derivative is `fderiv ℝ (...) x v`, and the convolution uses volume measure. This identifies the classical derivative of the mollified function with the mollification of the weak derivative.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem fderiv_convolution_eq_of_hasWeakDerivAlong {E : Type*} [NormedAddCommGroup E]
--       [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
--       {f g : E → ℝ} {v : E} (h : HasWeakDerivAlong f g v) (φ : ContDiffBump (0 : E)) (x : E) :
--       fderiv ℝ (convolution (φ.normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x v =
--         convolution (φ.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Mollification`](https://prove2.me/theorems/480cb5f8-8cac-4e12-bd32-870acaf66221).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Next: [`quotient_pairing_tendsto`](https://prove2.me/theorems/93835bcb-bdbc-4706-adbe-19b48ce839be).
--
--   [Source excerpt, lines 25–29](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Mollification.lean#L25-L29) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Mollification.lean#L23-L83 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Mollification`, declaration `FunctionalInequalities.Analysis.fderiv_convolution_eq_of_hasWeakDerivAlong`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Mollification

open MeasureTheory Set Filter

theorem FunctionalInequalities.Analysis.fderiv_convolution_eq_of_hasWeakDerivAlong_readable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f g : E → ℝ} {v : E} (h : HasWeakDerivAlong f g v) (φ : ContDiffBump (0 : E)) (x : E) :
    fderiv ℝ (convolution (φ.normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x v =
      convolution (φ.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by sorry
