-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussian_product_latent_map_readable
-- name    : FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_latent_map_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:00.476028+00:00
-- url     : https://prove2.me/theorems/3d05d9ff-f20e-4259-8e76-31eb720af291
-- title:
--   Latent Product Representation of Smoothed Linear Images
-- statement:
--   This statement identifies a Gaussian-smoothed linear image through a latent representation.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $ρ$ be a probability measure, let $μ$ be a measure on $E$, and let $g:E\to E$ be measurable with `map g ρ = μ`. Let $S:E\to E$ be continuous linear, and let $s>0$. Then
--
--   $$
--   \operatorname{map}\bigl((y,z)\mapsto S(g(y))+z\bigr)\bigl(ρ\otimes\operatorname{gaussianLaw}(s)\bigr)
--   =
--   \operatorname{smoothedLaw}(\operatorname{map}(S,μ),s).
--   $$
--
--   The identity provides a coupling-level description of Gaussian smoothing for later integral and Stein calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gaussian_product_latent_map (ρ μ : Measure E) [IsProbabilityMeasure ρ]
--       (g : E → E) (hg : Measurable g) (hmap : ρ.map g = μ)
--       (S : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) :
--       (ρ.prod (gaussianLaw (V := E) s)).map (fun p => S (g p.1) + p.2) =
--         smoothedLaw (μ.map S) s
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/GaussianSmoothing/LinearImage`](https://prove2.me/theorems/65252c7c-8be3-4f9a-a8e7-be00ac3deb3b).
--
--   Definition modules: [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575).
--
--   [Source excerpt, lines 31–35](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/LinearImage.lean#L31-L35) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/LinearImage.lean#L31-L47 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.LinearImage`, declaration `FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_latent_map`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_LinearImage

open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussian_product_latent_map_readable (ρ μ : Measure E) [IsProbabilityMeasure ρ]
    (g : E → E) (hg : Measurable g) (hmap : ρ.map g = μ)
    (S : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) :
    (ρ.prod (gaussianLaw (V := E) s)).map (fun p => S (g p.1) + p.2) =
      smoothedLaw (μ.map S) s := by sorry
