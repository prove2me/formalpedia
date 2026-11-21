-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_diffusion_diff_lintegral_sq_bound
-- name    : LevyStochCalc.Ito.Picard.diffusion_diff_lintegral_sq_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T21:55:56.96925+00:00
-- url     : https://prove2.me/theorems/94c34718-3652-41c9-9c43-857ce524515e
-- title:
--   diffusion diff lintegral sq bound
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.diffusion_diff_lintegral_sq_bound` is extracted from `LevyStochCalc.Ito.PicardOutputWeighting`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki weighting and the per-component difference bounds

The Bielecki norm with rate `β` dominates the second moment at each time of `[0, T]` after
reweighting by `e^{2βs}`, and the doubly-integrated energy over `[0, t]` by
`e^{2βt}/(2β)`, the factor `1/(2β)` being what makes the Picard rate small for large `β`.
Combined with the Lipschitz bounds on the coefficients this bounds the drift, diffusion and
jump components of the difference of two Picard steps by the energy of the difference of the
two frozen paths.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

section Weighting

omit [MeasurableSpace E] in

theorem _root_.LevyStochCalc.Ito.Picard.diffusion_diff_lintegral_sq_bound
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_σ : ℝ} (hL_σ_nn : 0 ≤ L_σ)
    (h_σ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
      (∑ i : Fin n, ∑ j : Fin d, (coeffs.σ s x₁ i j - coeffs.σ s x₂ i j) ^ 2)
        ≤ L_σ ^ 2 * ‖x₁ - x₂‖ ^ 2)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ∑ i : Fin n,
        (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
          - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L_σ ^ 2))
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
