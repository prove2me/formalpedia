-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_integrableOn_window_univ_of_lintegral_lt_top
-- name    : LevyStochCalc.Ito.JumpFormula.integrableOn_window_univ_of_lintegral_lt_top
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T13:25:53.403534+00:00
-- url     : https://prove2.me/theorems/b04f0c7c-eac1-4b83-926b-5cf4153f57f0
-- title:
--   integrableOn window univ of lintegral lt top
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.integrableOn_window_univ_of_lintegral_lt_top` is extracted from `LevyStochCalc.Ito.ItoLevyFormulaGeneral`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyFormulaGeneral_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy formula for a jump diffusion

The Itô–Lévy formula for a jointly `C²` state function of a jump diffusion, relative to the
filtration of the solution's SDE data, with no bound on the derivatives of the state function:
the only hypotheses beyond the SDE data are the joint measurability of the coefficients, the
window energy of the drift along the path, and the admissibility of the two derived integrands
`(∇u)ᵀσ` and `u(x + γ) − u(x)` together with the integrability of the compensator drift.

The proof cuts the state function off outside a ball, applies the bounded-derivative formula to
the cut-off, and transfers every term back on the event that the path stays in the ball over the
window: the continuous side term by term, the jump side as a sum, through the arrival-time jump
relation of the solution. Almost every path stays in some ball.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_general_of_leftLim` —
  the residual form along a solution with càdlàg paths at every sample point.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_general` — the residual
  form along any jump diffusion, through its càdlàg representative.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_general` — the four-term form.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Probability LevyStochCalc.Ito.Setting LevyStochCalc.Ito.JumpSplitting
open LevyStochCalc.Ito.CutoffPath LevyStochCalc.Poisson.Compensated

universe u v

section Transfers

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {n : ℕ}

variable [SigmaFinite ν]

theorem _root_.LevyStochCalc.Ito.JumpFormula.integrableOn_window_univ_of_lintegral_lt_top {g : ℝ × E → ℝ} (hg : Measurable g) {T : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤) :
    IntegrableOn g (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E))
      (LevyStochCalc.Poisson.referenceIntensity ν) := by sorry
