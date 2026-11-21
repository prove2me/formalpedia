-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_jump_diff_lipschitz_sq_componentwise
-- name    : LevyStochCalc.Ito.Picard.picardStep_jump_diff_lipschitz_sq_componentwise
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:32:35.287037+00:00
-- url     : https://prove2.me/theorems/5fef6ae1-afba-4b03-bbfe-a345903132aa
-- title:
--   picardStep jump diff lipschitz sq componentwise
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.picardStep_jump_diff_lipschitz_sq_componentwise` is extracted from `LevyStochCalc.Ito.PicardStochasticLipschitz`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

end LevyStochCalc.Ito.Picard

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

theorem _root_.LevyStochCalc.Ito.Picard.picardStep_jump_diff_lipschitz_sq_componentwise
    {n d : ℕ}
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_γ : ℝ} (_hL_γ_nn : 0 ≤ L_γ)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (i : Fin n)
    -- L²-in-e Lipschitz hypothesis on γ (ENNReal form, pointwise in (s, ω)):
    (h_γ_lip : ∀ s : ℝ, ∀ ω : Ω,
      ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
        ≤ ENNReal.ofReal (L_γ ^ 2) * (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2)
    -- Hypothesis bundles for `picardStep_jump` well-typedness — X side:
    (hX_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (hX_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ
        (fun ω s e => coeffs.γ s (X s ω) e i))
    (hX_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    -- Hypothesis bundles — Y side:
    (hY_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (hY_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ
        (fun ω s e => coeffs.γ s (Y s ω) e i))
    (hY_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖picardStep_jump (E := E) N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq T ω i
            - picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq T ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (L_γ ^ 2) *
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
