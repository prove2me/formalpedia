-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_cross_increment_integrable
-- name    : LevyStochCalc.Brownian.Ito.cross_increment_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T17:12:06.144706+00:00
-- url     : https://prove2.me/theorems/c3f384db-1478-4de6-bfb9-2ad660fdce70
-- title:
--   cross increment integrable
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.cross_increment_integrable` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionIncrement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: increment expansions and the intermediate-time isometry

Diagonal and off-diagonal expectations of products of Brownian increments against
adapted weights, the Bochner expansion of the square of a simple integral clamped
at an intermediate time, and the isometry
`∫⁻ ‖simpleIntegral W H t‖₊² = ∫⁻ ∫⁻_{[0, t]} ‖H.eval‖₊²` it gives for every
intermediate time `t`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.cross_increment_integrable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (hab₁ : a₁ ≤ b₁) (ha₂ : 0 ≤ a₂) (hab₂ : a₂ ≤ b₂)
    (ξ₁ ξ₂ : Ω → ℝ) (hξ₁meas : Measurable ξ₁) (hξ₂meas : Measurable ξ₂)
    (M₁ : ℝ) (hbd₁ : ∀ ω, |ξ₁ ω| ≤ M₁) (M₂ : ℝ) (hbd₂ : ∀ ω, |ξ₂ ω| ≤ M₂) :
    MeasureTheory.Integrable
      (fun ω => (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω))) P := by sorry
