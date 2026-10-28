-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_fderiv_kernel_eq_readable
-- name    : FunctionalInequalities.Analysis.integral_fderiv_kernel_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:49.89919+00:00
-- url     : https://prove2.me/theorems/8b5ca05b-ad73-4f24-8770-85db445dfaf1
-- title:
--   Derivative Kernel Integration Identity
-- statement:
--   This technical lemma gives an integration-by-parts identity for a Lipschitz change of variables.
--
--   Let $E$ be a finite-dimensional real inner-product space equipped with its Borel measure. Let $F:E\to E$ be Lipschitz with constant bounded by $G\in[0,\infty)$, let $k:E\to\mathbb R$ be $C^1$ with compact support, let $x,v\in E$, and let $\ell:E\to\mathbb R$ be continuous linear. Then
--
--   $$
--   \int \mathrm Dk(t)[v]\,\ell(F(x-t))\,dt
--   =
--   \int k(t)\,\ell\!\left(DF(x-t)[v]\right)\,dt.
--   $$
--
--   The derivative $DF$ is `fderiv ℝ F` and is used pointwise in the displayed expression. The result is used to establish derivative formulas for mollified Lipschitz maps.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem integral_fderiv_kernel_eq
--       {F : E → E} {G : NNReal} (hF : LipschitzWith G F)
--       (k : E → ℝ) (hk : ContDiff ℝ 1 k) (hc : HasCompactSupport k)
--       (x v : E) (ℓ : E →L[ℝ] ℝ) :
--       (∫ t, fderiv ℝ k t v * ℓ (F (x - t))) =
--         ∫ t, k t * ℓ (fderiv ℝ F (x - t) v)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Mollification/Basic`](https://prove2.me/theorems/b351487c-eaef-4d4f-b656-728d01c5702d).
--
--   Previous: [`laplacian_convolution`](https://prove2.me/theorems/0855ca87-12f0-432a-bb25-ce692eba493f) · Next: [`hasFDerivAt_convolution_normed_of_lipschitz`](https://prove2.me/theorems/9ccb4a93-a981-4edd-a672-af4d66944fff).
--
--   [Source excerpt, lines 456–461](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L456-L461) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L456-L510 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `_private.FunctionalInequalities.Analysis.Mollification.Basic.0.FunctionalInequalities.Analysis.integral_fderiv_kernel_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]

theorem FunctionalInequalities.Analysis.integral_fderiv_kernel_eq_readable
    {F : E → E} {G : NNReal} (hF : LipschitzWith G F)
    (k : E → ℝ) (hk : ContDiff ℝ 1 k) (hc : HasCompactSupport k)
    (x v : E) (ℓ : E →L[ℝ] ℝ) :
    (∫ t, fderiv ℝ k t v * ℓ (F (x - t))) =
      ∫ t, k t * ℓ (fderiv ℝ F (x - t) v) := by sorry
