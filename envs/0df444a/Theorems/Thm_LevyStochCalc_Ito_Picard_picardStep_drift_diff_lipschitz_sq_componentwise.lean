-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_picardStep_drift_diff_lipschitz_sq_componentwise
-- name    : LevyStochCalc.Ito.Picard.picardStep_drift_diff_lipschitz_sq_componentwise
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:25:41.677111+00:00
-- url     : https://prove2.me/theorems/95e5fdc1-492c-4312-bdfe-96ff9a83dc6e
-- title:
--   picardStep drift diff lipschitz sq componentwise
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.picardStep_drift_diff_lipschitz_sq_componentwise` is extracted from `LevyStochCalc.Ito.PicardBieleckiNorm`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bielecki norm, the process space `S²`, and the drift step of Picard iteration

The Bielecki-weighted `L²` norm `‖X‖_{β,T} = sup_{t ∈ [0,T]} e^{-βt} (𝔼‖X_t‖²)^{1/2}` of a
process on `[0, T]`, the space `SBoundedProcess` of jointly measurable, progressively measurable,
almost surely càdlàg processes of finite norm at weight `0`, and the freeze of such a process at
the horizon, which leaves the norm unchanged and is `L²`-bounded at every later time.  The drift
component `picardStep_drift` of the Picard map is defined here, with its per-component difference
identities, its `L¹` Lipschitz bound, the Cauchy-Schwarz bound `(∫_0^t f)² ≤ t ∫_0^t f²` on a
window, and the per-component `L²` Lipschitz bound that follows from them.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace SBoundedProcess

end SBoundedProcess

omit [MeasurableSpace Ω] [MeasurableSpace E] in

theorem _root_.LevyStochCalc.Ito.Picard.picardStep_drift_diff_lipschitz_sq_componentwise
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω) (i : Fin n)
    (h_X_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_int : MeasureTheory.IntegrableOn
      (fun s => ‖X s ω - Y s ω‖) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_sq_L2 : MeasureTheory.MemLp
      (fun s => ‖X s ω - Y s ω‖) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))) :
    ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by sorry
