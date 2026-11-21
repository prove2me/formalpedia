-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_iSup_sq_norm_version_sub_le
-- name    : LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:35:53.915001+00:00
-- url     : https://prove2.me/theorems/462d74ca-7007-47ce-ad84-07655a1450f1
-- title:
--   lintegral iSup sq norm version sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le` is extracted from `LevyStochCalc.Ito.VectorItoVersionSup`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_VectorItoVersionSup_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The window supremum of the difference of two vector Itô versions

Two versions driven by different coefficients differ by a drift part, controlled pathwise by
Cauchy–Schwarz, and a martingale part, controlled by Doob's `L²` maximal inequality. Sampling the
paths on the dyadic points of the window turns the supremum into a countable one, which is all the
maximal inequality needs.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le` — the second moment of the
  window supremum of the difference, in terms of the coefficients' energies.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Helpers

variable {Ω : Type u}

variable [MeasurableSpace Ω] {P : Measure Ω}

end Helpers

section SupBound

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

include hcoord in

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le
    {H₁ H₂ : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm₁ : ∀ p k, Measurable (Function.uncurry (H₁ p k))}
    {hp₁ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₁ p k)}
    {hq₁ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {hm₂ : ∀ p k, Measurable (Function.uncurry (H₂ p k))}
    {hp₂ : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H₂ p k)}
    {hq₂ : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {b₁ b₂ : Fin n → Ω → ℝ → ℝ}
    (hbm₁ : ∀ p, Measurable (Function.uncurry (b₁ p)))
    (hbm₂ : ∀ p, Measurable (Function.uncurry (b₂ p)))
    (hbq₁ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hbq₂ : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₂ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X Y : ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ hcoord H₁ hm₁ hp₁ hq₁ X₀ b₁ X)
    (hY : IsVectorItoVersion W ℱ hcoord H₂ hm₂ hp₂ hq₂ X₀ b₂ Y)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Y (t : ℝ) ω - X (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n,
          (4 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖b₂ p ω s - b₁ p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖H₂ p k ω s - H₁ p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))) := by sorry
