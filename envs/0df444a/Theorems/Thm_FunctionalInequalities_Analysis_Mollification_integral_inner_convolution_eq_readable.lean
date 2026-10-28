-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Mollification_integral_inner_convolution_eq_readable
-- name    : FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:50.657987+00:00
-- url     : https://prove2.me/theorems/fd3d77b4-2913-4723-a4fd-5a1404fbf923
-- title:
--   Symmetry of Mollification in the Inner-Product Pairing
-- statement:
--   This is the symmetry identity for convolution by a normalized even bump.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, and let $E$ be a complete normed real inner-product space. Let $\varphi$ be a smooth bump centered at $0$. If $a:V\to E$ is integrable, and $b:V\to E$ is continuous and compactly supported, then
--
--   $$\int_V\left\langle(\varphi_{\mathrm{normed}}\ast a)(x),b(x)\right\に dm(x)
--   =\int_V\left\langle a(y),(\varphi_{\mathrm{normed}}\ast b)(y)\right\rangle\,dm(y).$$
--
--   The result transfers the mollifier between the two entries of the integrated inner product without reflecting the kernel.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Mollification`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_inner_convolution_eq {a b : V → E} (ha : Integrable a m) (hb : Continuous b)
--       (hbc : HasCompactSupport b) :
--       ∫ x, ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] a) x, b x⟫ ∂m =
--         ∫ y, ⟪a y, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] b) y⟫ ∂m
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Mollification/Basic`](https://prove2.me/theorems/b351487c-eaef-4d4f-b656-728d01c5702d).
--
--   Previous: [`tendsto_eLpNorm_convolution_sub`](https://prove2.me/theorems/3e5007ce-6906-4a04-82a9-55a0bdd821b3) · Next: [`gradient_convolution`](https://prove2.me/theorems/fe7a116d-bd27-498e-9e9e-354056906010).
--
--   [Source excerpt, lines 285–288](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L285-L288) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L282-L350 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (φ : ContDiffBump (0 : V))

theorem FunctionalInequalities.Analysis.Mollification.integral_inner_convolution_eq_readable {a b : V → E} (ha : Integrable a m) (hb : Continuous b)
    (hbc : HasCompactSupport b) :
    ∫ x, ⟪(φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] a) x, b x⟫ ∂m =
      ∫ y, ⟪a y, (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] b) y⟫ ∂m := by sorry
