-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_laplacian_mul_convolution_eq_readable
-- name    : FunctionalInequalities.KLS.LogConcave.integral_laplacian_mul_convolution_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:15.807742+00:00
-- url     : https://prove2.me/theorems/4e49d784-08a5-433a-989e-30d5dbb063cf
-- title:
--   Mollified Weak Laplacian Equation
-- statement:
--   This lemma transfers a weak weighted Laplacian equation through convolution.
--
--   Let $V$ be finite-dimensional and complete, let $m$ be an additive Haar measure, let $W:V\to\mathbb R$ and $F:V\to V$. Assume that every smooth compactly supported test function $f$ satisfies
--
--   $$
--   \int (\Delta f)W\,dm
--   =\int \langle\nabla f,WF\rangle\,dm+\int fW\,dm.
--   $$
--
--   Let $\eta$ be a smooth bump equal to $1$ on the closed ball of radius $R+1$, assume $\eta W$ and $(\eta W)F$ are integrable, and let $\phi$ be a normalized smooth bump with outer radius at most $1$. For every smooth compactly supported $g$ supported in the closed ball of radius $R$, the convolutions satisfy
--
--   $$
--   \int (\Delta g)\,\bigl(\phi\ast(\eta W)\bigr)\,dm
--   =
--   \int \left\langle\nabla g,\phi\ast(\eta WF)\right\rangle\,dm
--   +\int g\,\bigl(\phi\ast(\eta W)\bigr)\,dm.
--   $$
--
--   The convolution is the measure-dependent normalized convolution represented by `convolution` and `ContDiffBump.normed`. This is a technical mollification identity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem integral_laplacian_mul_convolution_eq {W : V → ℝ} {F : V → V}
--       (hW : ∀ f : V → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
--         ∫ x, Laplacian.laplacian f x * W x ∂m =
--           ∫ x, ⟪gradient f x, W x • F x⟫ ∂m + ∫ x, f x * W x ∂m)
--       {R : ℝ} (η : ContDiffBump (0 : V)) (hη : R + 1 ≤ η.rIn)
--       (hw : Integrable (fun x => η x * W x) m) (hG : Integrable (fun x => (η x * W x) • F x) m)
--       (φ : ContDiffBump (0 : V)) (hφ : φ.rOut ≤ 1) {g : V → ℝ} (hg : ContDiff ℝ ∞ g)
--       (hgc : HasCompactSupport g) (hgR : tsupport g ⊆ closedBall 0 R) :
--       ∫ x, Laplacian.laplacian g x *
--           (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m =
--         ∫ x, ⟪gradient g x,
--             (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x⟫ ∂m +
--           ∫ x, g x * (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/InteriorRegularity`](https://prove2.me/theorems/79e586aa-54d4-4c9a-ac32-31116ce1ca0f).
--
--   Supporting theorems: [`gradient_convolution`](https://prove2.me/theorems/fe7a116d-bd27-498e-9e9e-354056906010), [`integral_inner_convolution_eq`](https://prove2.me/theorems/fd3d77b4-2913-4723-a4fd-5a1404fbf923), [`laplacian_convolution`](https://prove2.me/theorems/0855ca87-12f0-432a-bb25-ce692eba493f).
--
--   Previous: [`norm_toLp_smul_gradient_le`](https://prove2.me/theorems/498d247b-5ee4-41ec-a4b1-bd5e9cc8d247) · Next: [`integral_laplacian_mul_tiltedDensity_mul`](https://prove2.me/theorems/f41686bf-c848-414b-978b-8c5c05a45d74).
--
--   [Source excerpt, lines 245–257](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean#L245-L257) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean#L238-L335 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity`, declaration `_private.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity.0.FunctionalInequalities.KLS.LogConcave.integral_laplacian_mul_convolution_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity

open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped ContDiff RealInnerProductSpace Convolution ENNReal
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.KLS.LogConcave.integral_laplacian_mul_convolution_eq_readable {W : V → ℝ} {F : V → V}
    (hW : ∀ f : V → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ∫ x, Laplacian.laplacian f x * W x ∂m =
        ∫ x, ⟪gradient f x, W x • F x⟫ ∂m + ∫ x, f x * W x ∂m)
    {R : ℝ} (η : ContDiffBump (0 : V)) (hη : R + 1 ≤ η.rIn)
    (hw : Integrable (fun x => η x * W x) m) (hG : Integrable (fun x => (η x * W x) • F x) m)
    (φ : ContDiffBump (0 : V)) (hφ : φ.rOut ≤ 1) {g : V → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hgR : tsupport g ⊆ closedBall 0 R) :
    ∫ x, Laplacian.laplacian g x *
        (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m =
      ∫ x, ⟪gradient g x,
          (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => (η y * W y) • F y) x⟫ ∂m +
        ∫ x, g x * (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] fun y => η y * W y) x ∂m := by sorry
