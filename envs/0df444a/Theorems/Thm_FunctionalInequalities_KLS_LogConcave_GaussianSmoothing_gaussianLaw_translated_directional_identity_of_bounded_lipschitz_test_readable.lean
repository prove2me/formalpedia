-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_translated_directional_identity_of_bounded_lipschitz_test_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_translated_directional_identity_of_bounded_lipschitz_test_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:50.596184+00:00
-- url     : https://prove2.me/theorems/c0deab00-4b66-4ff2-9322-12a13e5f7645
-- title:
--   Translated Gaussian Directional Integration by Parts
-- statement:
--   This statement gives the translated form of Gaussian integration by parts.
--
--   Let $n\in\mathbb N$, let $h:\mathbb R^n\to\mathbb R$ be $C^1$ and globally Lipschitz, and suppose $\|h(x)\|\le C$ for every $x$. For $a,v\in\mathbb R^n$ and $s>0$, both functions $z\mapsto\langle z,v\rangle h(a+z)$ and $z\mapsto D_vh(a+z)$ are integrable with respect to `gaussianLaw s`, and
--
--   $$
--   \int \langle z,v\rangle h(a+z)\,d\gamma_s(z)
--   =
--   (2s)^{-1}\int D_vh(a+z)\,d\gamma_s(z).
--   $$
--
--   The result is a reusable translated-noise identity for product-coupling arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gaussianLaw_translated_directional_identity_of_bounded_lipschitz_test {n : ℕ}
--       {h : EuclideanSpace ℝ (Fin n) → ℝ} {Lh : NNReal}
--       (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
--       (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
--       (a v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
--       Integrable (fun z => ⟪z,v⟫ * h (a+z)) (gaussianLaw s) ∧
--       Integrable (fun z => fderiv ℝ h (a+z) v) (gaussianLaw s) ∧
--       (∫ z, ⟪z,v⟫ * h (a+z) ∂(gaussianLaw s)) =
--         (2*s)⁻¹ * ∫ z, fderiv ℝ h (a+z) v ∂(gaussianLaw s)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   Supporting theorems: [`gaussianLaw_directional_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/123bb3a0-2332-4e67-a78a-7bf12553f53a).
--
--   Previous: [`gaussianLaw_directional_identity_of_bounded_lipschitz_test`](https://prove2.me/theorems/123bb3a0-2332-4e67-a78a-7bf12553f53a).
--
--   [Source excerpt, lines 545–553](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L545-L553) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean#L545-L565 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_translated_directional_identity_of_bounded_lipschitz_test`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments

open MeasureTheory
open scoped ContDiff RealInnerProductSpace

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_translated_directional_identity_of_bounded_lipschitz_test_readable {n : ℕ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {Lh : NNReal}
    (hh : ContDiff ℝ 1 h) (hhLip : LipschitzWith Lh h)
    (C : ℝ) (hbound : ∀ x, ‖h x‖ ≤ C)
    (a v : EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : 0 < s) :
    Integrable (fun z => ⟪z,v⟫ * h (a+z)) (gaussianLaw s) ∧
    Integrable (fun z => fderiv ℝ h (a+z) v) (gaussianLaw s) ∧
    (∫ z, ⟪z,v⟫ * h (a+z) ∂(gaussianLaw s)) =
      (2*s)⁻¹ * ∫ z, fderiv ℝ h (a+z) v ∂(gaussianLaw s) := by sorry
