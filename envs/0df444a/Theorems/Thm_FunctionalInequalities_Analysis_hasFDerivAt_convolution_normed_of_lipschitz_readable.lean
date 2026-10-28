-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasFDerivAt_convolution_normed_of_lipschitz_readable
-- name    : FunctionalInequalities.Analysis.hasFDerivAt_convolution_normed_of_lipschitz_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:54.246089+00:00
-- url     : https://prove2.me/theorems/9ccb4a93-a981-4edd-a672-af4d66944fff
-- title:
--   Derivative of a Mollified Lipschitz Map
-- statement:
--   This establishes the derivative formula for convolution with a normalized smooth bump.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel structure. Let $F:E\to E$ be Lipschitz with Lipschitz bound $G\in[0,\infty)$, let $\varphi$ be a smooth compactly supported bump centered at $0$, and let $x\in E$. Then the convolution of $F$ with the normalized bump $\varphi^{\mathrm{norm}}$ has a Fréchet derivative at $x$ given by the convolution of the almost-everywhere derivative of $F$:
--
--   $$
--   D\bigl(\varphi^{\mathrm{norm}}\!\ast F\bigr)(x)
--   =
--   \bigl(\varphi^{\mathrm{norm}}\!\ast DF\bigr)(x).
--   $$
--
--   In Lean, the convolution uses `ContinuousLinearMap.lsmul`, volume measure, and `fderiv ℝ F`. This is a supporting result for mollification identities.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasFDerivAt_convolution_normed_of_lipschitz
--       {F : E → E} {G : NNReal} (hF : LipschitzWith G F) (φ : ContDiffBump (0 : E)) (x : E) :
--       HasFDerivAt (φ.normed (volume : Measure E) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] F)
--         ((φ.normed (volume : Measure E) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
--           fderiv ℝ F) x) x
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Mollification/Basic`](https://prove2.me/theorems/b351487c-eaef-4d4f-b656-728d01c5702d).
--
--   Supporting theorems: [`integral_fderiv_kernel_eq`](https://prove2.me/theorems/8b5ca05b-ad73-4f24-8770-85db445dfaf1).
--
--   Previous: [`integral_fderiv_kernel_eq`](https://prove2.me/theorems/8b5ca05b-ad73-4f24-8770-85db445dfaf1).
--
--   [Source excerpt, lines 516–520](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L516-L520) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L512-L557 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.hasFDerivAt_convolution_normed_of_lipschitz`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

open MeasureTheory
open scoped Convolution
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]

theorem FunctionalInequalities.Analysis.hasFDerivAt_convolution_normed_of_lipschitz_readable
    {F : E → E} {G : NNReal} (hF : LipschitzWith G F) (φ : ContDiffBump (0 : E)) (x : E) :
    HasFDerivAt (φ.normed (volume : Measure E) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] F)
      ((φ.normed (volume : Measure E) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        fderiv ℝ F) x) x := by sorry
