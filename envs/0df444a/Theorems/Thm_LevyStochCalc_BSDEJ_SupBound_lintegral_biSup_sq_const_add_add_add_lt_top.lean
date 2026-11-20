-- Prove2me | Theorems.Thm_LevyStochCalc_BSDEJ_SupBound_lintegral_biSup_sq_const_add_add_add_lt_top
-- name    : LevyStochCalc.BSDEJ.SupBound.lintegral_biSup_sq_const_add_add_add_lt_top
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T14:58:47.874018+00:00
-- url     : https://prove2.me/theorems/f0d536d9-d01d-4d34-b53b-1bb584517e3b
-- title:
--   lintegral biSup sq const add add add lt top
-- statement:
--   The source theorem `LevyStochCalc.BSDEJ.SupBound.lintegral_biSup_sq_const_add_add_add_lt_top` is extracted from `LevyStochCalc.BSDEJ.SupBound`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The `S²` norm of a sum of a constant, two martingales and a drift

The solution space `S²` of a backward equation asks for
`∫⁻ ω, ⨆ t ∈ [0, T], ‖Y t ω‖ₑ² ∂μ < ⊤`, a supremum over the window taken *inside* the square,
while Doob's `L²` maximal inequality
(`LevyStochCalc.Probability.lintegral_iSup_sq_le_of_martingale`) is stated with the square
outside a supremum over the subtype `↥(Set.Icc 0 T)`. The two shapes agree, because squaring
commutes with suprema in `ℝ≥0∞`, and the resulting bound is stable under the decomposition
`Y = c + M₁ + M₂ + A` of a Picard iterate into a constant, two stochastic integrals and a
time integral of the generator.

## Main statements

* `biSup_sq_eq_iSup_subtype_sq` — the two shapes of the squared supremum over `[0, T]` agree.
* `lintegral_biSup_sq_le_of_martingale` — Doob's `L²` maximal inequality in the `S²` shape.
* `lintegral_biSup_sq_add_le` — the `S²` seminorm is subadditive up to a factor `2`.
* `lintegral_biSup_sq_const_add_add_add_lt_top` — a sum of a constant and three processes of
  finite `S²` seminorm has finite `S²` seminorm.
* `lintegral_biSup_sq_setIntegral_le` — the `S²` seminorm of a time integral, by Cauchy–Schwarz.
* `lintegral_biSup_sq_const_mul` — the `S²` seminorm of a scalar multiple of a process.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.SupBound

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Squares and suprema in `ℝ≥0∞` -/

/-! ### Doob's `L²` maximal inequality in the `S²` shape -/

/-! ### Subadditivity of the `S²` seminorm -/

theorem _root_.LevyStochCalc.BSDEJ.SupBound.lintegral_biSup_sq_const_add_add_add_lt_top [IsFiniteMeasure μ] (c : ℝ)
    (M₁ M₂ A : ℝ → Ω → ℝ) (T : ℝ)
    (hM₁ : AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M₁ t ω‖₊ : ℝ≥0∞) ^ 2) μ)
    (hM₂ : AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M₂ t ω‖₊ : ℝ≥0∞) ^ 2) μ)
    (hA : AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2) μ)
    (h₁ : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M₁ t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤)
    (h₂ : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M₂ t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤)
    (h₃ : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
        (‖c + M₁ t ω + M₂ t ω + A t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤ := by sorry
