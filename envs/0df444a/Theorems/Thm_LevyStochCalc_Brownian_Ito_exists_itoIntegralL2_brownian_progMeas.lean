-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_itoIntegralL2_brownian_progMeas
-- name    : LevyStochCalc.Brownian.Ito.exists_itoIntegralL2_brownian_progMeas
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T16:41:57.478055+00:00
-- url     : https://prove2.me/theorems/258595fd-d162-42bc-871d-9bc84da0c1e9
-- title:
--   exists itoIntegralL2 brownian progMeas
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.exists_itoIntegralL2_brownian_progMeas` is extracted from `LevyStochCalc.Brownian.ItoL2CompletionExistence`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: existence of the `L²` integral

Adaptedness, integrability and conditional-expectation identities for the
simple-integrand Brownian integral, and the existence statements they yield for
the `L²` Itô integral of a bounded, respectively progressively measurable and
square-integrable, integrand against a Brownian motion `W` on a Brownian
filtration `ℱ`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

set_option maxHeartbeats 1600000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.

theorem _root_.LevyStochCalc.Brownian.Ito.exists_itoIntegralL2_brownian_progMeas
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Mlp : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑Mlp : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by sorry
