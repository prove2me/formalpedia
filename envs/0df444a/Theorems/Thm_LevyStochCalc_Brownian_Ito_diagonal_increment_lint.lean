-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_diagonal_increment_lint
-- name    : LevyStochCalc.Brownian.Ito.diagonal_increment_lint
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T16:45:20.155687+00:00
-- url     : https://prove2.me/theorems/9f063f07-9d94-4a5f-b71b-efd572c0e037
-- title:
--   diagonal increment lint
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.diagonal_increment_lint` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionIncrement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F001

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

theorem _root_.LevyStochCalc.Brownian.Ito.diagonal_increment_lint
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (ξ : Ω → ℝ)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) ξ) :
    ∫⁻ ω, (‖ξ ω * (W.W b ω - W.W a ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal (b - a) * ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by sorry
