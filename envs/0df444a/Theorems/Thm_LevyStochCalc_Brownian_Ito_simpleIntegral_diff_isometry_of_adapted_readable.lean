-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_simpleIntegral_diff_isometry_of_adapted_readable
-- name    : LevyStochCalc.Brownian.Ito.simpleIntegral_diff_isometry_of_adapted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:00.761528+00:00
-- url     : https://prove2.me/theorems/2683d1bc-8d01-4352-8fe2-981705a37ca4
-- title:
--   Difference Isometry for Adapted Simple Integrals
-- statement:
--   Let $W$ be a Brownian motion with Brownian filtration $ℱ$. Let $G₁,G₂$ be simple predictable integrands, possibly with different horizons, and assume all their coefficients are strongly measurable at the relevant filtration times. For $t≥0$,
--
--   $$\int_Ω\|I_{G₁}(t,ω)-I_{G₂}(t,ω)\|^2\,dP
--   =\int_Ω\int_{[0,t]}\|G₁(s,ω)-G₂(s,ω)\|^2\,ds\,dP.$$
--
--   Both sides are `ENNReal` integrals in $[0,∞]$. The result extends the intermediate-time Itô isometry to simple integrands whose horizons need not coincide.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem simpleIntegral_diff_isometry_of_adapted
--       {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
--       {T₁ T₂ : ℝ} (G₁ : SimplePredictable Ω T₁) (G₂ : SimplePredictable Ω T₂)
--       (h₁ : ∀ i : Fin G₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ (G₁.partition i.castSucc)) (G₁.ξ i))
--       (h₂ : ∀ i : Fin G₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ (G₂.partition i.castSucc)) (G₂.ξ i))
--       {t : ℝ} (ht : 0 ≤ t) :
--       ∫⁻ ω,
--           (‖simpleIntegral W G₁ t ω - simpleIntegral W G₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
--         = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
--             (‖G₁.eval s ω - G₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand`](https://prove2.me/theorems/09c55224-b261-4948-9982-f2ec68361149).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Previous: [`SimplePredictable.lintegral_eval_sq_lt_top`](https://prove2.me/theorems/1a3d860d-d849-45a8-9155-ad2dbfbcdfa6) · Next: [`stochasticIntegralBrownian_eval_simple`](https://prove2.me/theorems/cae7fbf2-3586-459d-92c8-a9b6a264de7f).
--
--   [Source excerpt, lines 125–137](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean#L125-L137) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean#L123-L166 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand`, declaration `LevyStochCalc.Brownian.Ito.simpleIntegral_diff_isometry_of_adapted`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.simpleIntegral_diff_isometry_of_adapted_readable
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T₁ T₂ : ℝ} (G₁ : SimplePredictable Ω T₁) (G₂ : SimplePredictable Ω T₂)
    (h₁ : ∀ i : Fin G₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G₁.partition i.castSucc)) (G₁.ξ i))
    (h₂ : ∀ i : Fin G₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G₂.partition i.castSucc)) (G₂.ξ i))
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω,
        (‖simpleIntegral W G₁ t ω - simpleIntegral W G₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖G₁.eval s ω - G₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
