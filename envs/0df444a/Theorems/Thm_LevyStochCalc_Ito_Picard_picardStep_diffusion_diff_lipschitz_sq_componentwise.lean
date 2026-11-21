-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_diffusion_diff_lipschitz_sq_componentwise
-- name    : LevyStochCalc.Ito.Picard.picardStep_diffusion_diff_lipschitz_sq_componentwise
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:30:42.020481+00:00
-- url     : https://prove2.me/theorems/a41635c1-8061-4189-9d89-1adb8223bfcf
-- title:
--   picardStep diffusion diff lipschitz sq componentwise
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.picardStep_diffusion_diff_lipschitz_sq_componentwise` is extracted from `LevyStochCalc.Ito.PicardStochasticLipschitz`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F000
import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F001
import Mathlib.Algebra.Order.Chebyshev

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Lipschitz estimates for the stochastic components of the Picard map

The `L²`-isometry `𝔼|∫_0^T H₁ dW - ∫_0^T H₂ dW|² = 𝔼 ∫_0^T |H₁ - H₂|² ds` for the difference of
two Brownian Itô integrals, the discrete Cauchy-Schwarz inequality and the `ℝ≥0∞` norm-square
identities it is combined with, and the resulting per-component `L²` Lipschitz bounds for the
diffusion and the jump component of the Picard map in terms of the Lipschitz constants of `σ` and
`γ`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

variable {Ω : Type*} [MeasurableSpace Ω]

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace E] in

theorem _root_.LevyStochCalc.Ito.Picard.picardStep_diffusion_diff_lipschitz_sq_componentwise
    {n d : ℕ}
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_σ : ℝ} (_hL_σ_nn : 0 ≤ L_σ)
    -- Componentwise Lipschitz hypothesis on σ (matches `JumpDiffusionCoeffs.IsLipschitz`):
    -- `∑_{i,j} (σ(s, x₁)_{ij} - σ(s, x₂)_{ij})² ≤ L_σ² · ‖x₁ - x₂‖²`
    (h_σ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
      (∑ i : Fin n, ∑ j : Fin d,
        (coeffs.σ s x₁ i j - coeffs.σ s x₂ i j) ^ 2)
        ≤ L_σ ^ 2 * ‖x₁ - x₂‖ ^ 2)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (i : Fin n)
    -- Per-(i', j) measurability / progressive-measurability / L²
    -- hypotheses for σ along X and Y, threaded to `picardStep_diffusion`.
    (h_σ_meas_X : ∀ i' : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i' j)))
    (h_σ_meas_Y : ∀ i' : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i' j)))
    (h_σ_progMeas_X : ∀ i' : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X s ω) i' j))
    (h_σ_progMeas_Y : ∀ i' : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (Y s ω) i' j))
    (h_σ_sq_X : ∀ i' : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i' j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_σ_sq_Y : ∀ i' : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (Y s ω) i' j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X T ω i
              - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y T ω i‖₊
            : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal ((d : ℝ) * L_σ ^ 2) *
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
