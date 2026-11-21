-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_bielecki_contraction_tight
-- name    : LevyStochCalc.Ito.Picard.picardStep_bielecki_contraction_tight
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:06:43.323361+00:00
-- url     : https://prove2.me/theorems/dd9dc9bb-4a11-49ab-a208-5810d665893e
-- title:
--   picardStep bielecki contraction tight
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.picardStep_bielecki_contraction_tight` is extracted from `LevyStochCalc.Ito.PicardBieleckiContractionTight`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContraction_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Picard contraction at the literature-tight rate

The refinement of the Bielecki-norm contraction estimate that takes the diffusion and jump bounds
in their tight form, without the redundant time factor, giving the constant `3 n L² (T + 2)` in
place of `9 n L² T` and hence the contraction rate `3 n L² (T + 2) / (2β)`; together with the
threshold `3 n L² (T + 2) < 2β` under which that rate is `< 1`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

set_option maxHeartbeats 4000000 in
-- Same contraction chain as `picardStep_bielecki_contraction`, with the tighter
-- constant tracked through every step; it exceeds the default budget.

theorem _root_.LevyStochCalc.Ito.Picard.picardStep_bielecki_contraction_tight
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L : ℝ} (hL_nn : 0 ≤ L)
    -- μ-Lipschitz (componentwise; used inside the drift lintegral bound):
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (T : ℝ) (_hT : 0 < T)
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_X : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_Y : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    -- Drift bound's a.e. hypotheses (must hold at every `t ∈ [0, T]`):
    (h_drift_bound_ae : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        ≤ (n : ℝ) * L ^ 2 * t *
            ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    (h_drift_inner_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, 0 ≤
      ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    -- **Tight σ-step lintegral bound** (no `t` factor — the
    -- redundant `n · t` padding from the loose version has been
    -- removed; only the natural `n L²` constant remains):
    (h_σ_step_bound_tight : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
          - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2) *
          ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P)
    -- **Tight γ-step lintegral bound** (no `t` factor — analogous
    -- removal of the `n · t` padding):
    (h_γ_step_bound_tight : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2) *
          ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P)
    -- AEMeasurability of the three component sum-of-squares ofReal functions,
    -- needed to split the triple-term lintegral on the RHS of
    -- `picardStep_diff_lintegral_sum_sq_le`.
    (h_drift_ofReal_aemeas : ∀ t : ℝ, AEMeasurable (fun ω : Ω => ENNReal.ofReal
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)) P)
    (h_diff_ofReal_aemeas : ∀ t : ℝ, AEMeasurable (fun ω : Ω => ENNReal.ofReal
      (∑ i : Fin n, ((picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
          - picardStep_diffusion W ℱ hℱW coeffs Y
              h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)) P)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep W N ℱ hℱW hℱN coeffs X x₀
          h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        - picardStep W N ℱ hℱW hℱN coeffs Y x₀
          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
    ≤ ENNReal.ofReal (3 * (n : ℝ) * L ^ 2 * (T + 2)) *
        ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t,
          ‖X s ω - Y s ω‖ ^ 2) ∂P := by sorry
