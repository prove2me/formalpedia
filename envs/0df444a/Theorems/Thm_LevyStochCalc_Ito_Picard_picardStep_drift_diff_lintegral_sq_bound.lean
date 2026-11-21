-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_drift_diff_lintegral_sq_bound
-- name    : LevyStochCalc.Ito.Picard.picardStep_drift_diff_lintegral_sq_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:29:19.158751+00:00
-- url     : https://prove2.me/theorems/6bd800d9-c731-48f5-93e6-8a276f1a168c
-- title:
--   picardStep drift diff lintegral sq bound
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.picardStep_drift_diff_lintegral_sq_bound` is extracted from `LevyStochCalc.Ito.PicardStepMap`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Picard map for jump-diffusion SDEs

The vector-norm and `ω`-integrated forms of the drift Lipschitz estimate; the Bielecki
exponential-weight calculus `∫_0^t e^{2βs} ds = (e^{2βt} - 1) / (2β)` together with the
weighted-integral bound and the contraction-rate threshold it yields; the joint measurability of
the coefficients `σ` and `γ` composed with a process; and the Picard map `picardStep` itself, the
sum of the initial value, the drift integral, the Brownian component `picardStep_diffusion` and
the compensated-Poisson component `picardStep_jump`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace E] in

theorem _root_.LevyStochCalc.Ito.Picard.picardStep_drift_diff_lintegral_sq_bound
    {n d : ℕ} (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (_hL_μ_nn : 0 ≤ L_μ)
    (_h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t)
    -- Almost-everywhere integrability hypotheses (the pointwise bound only
    -- holds for ω with all integrands well-defined):
    (h_bound_ae : ∀ᵐ ω ∂P,
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        ≤ (n : ℝ) * L_μ ^ 2 * t *
            ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    -- Nonnegativity of the per-ω inner integral (for ENNReal conversion):
    (h_inner_nn : ∀ᵐ ω ∂P, 0 ≤
      ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P
    ≤ ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
        ∫⁻ ω, ENNReal.ofReal
          (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P := by sorry
