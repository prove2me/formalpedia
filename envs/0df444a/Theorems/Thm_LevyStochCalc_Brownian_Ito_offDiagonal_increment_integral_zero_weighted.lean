-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_offDiagonal_increment_integral_zero_weighted
-- name    : LevyStochCalc.Brownian.Ito.offDiagonal_increment_integral_zero_weighted
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:05:57.164622+00:00
-- url     : https://prove2.me/theorems/83ec0e2a-ac78-423f-b7dd-cce260a85f9c
-- title:
--   offDiagonal increment integral zero weighted
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.offDiagonal_increment_integral_zero_weighted` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionCompensator`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionCompensator_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the compensated square of a simple integral

Weighted off-diagonal vanishing for products of Brownian increments, the clamped
expansion of the square of a difference of simple integrals, and the martingale
property of the compensated square
`(simpleIntegral W H t)² − ∫_{[0, t]} (H.eval u)² du` with respect to the
filtration `ℱ`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.offDiagonal_increment_integral_zero_weighted
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (h₁ : a₁ < b₁) (h₁₂ : b₁ ≤ a₂) (h₂ : a₂ < b₂)
    (ξ₁ ξ₂ g : Ω → ℝ)
    (hadapt₁ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) ξ₁)
    (hadapt₂ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₂)
    (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) g) :
    ∫ ω, g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω))) ∂P
      = 0 := by sorry
