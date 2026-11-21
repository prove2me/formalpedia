-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_pairing_cell_eq_zero
-- name    : LevyStochCalc.Brownian.Ito.pairing_cell_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:02:48.567715+00:00
-- url     : https://prove2.me/theorems/1e5cdd3d-42b0-4d04-8744-97296a871d79
-- title:
--   pairing cell eq zero
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.pairing_cell_eq_zero` is extracted from `LevyStochCalc.Brownian.PRPCell`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPCell_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One window of the Brownian predictable representation

A square-integrable weight orthogonal to every Itô integral, multiplied by a bounded weight
measurable before a window and having mean zero, stays orthogonal to the character of the
Brownian increment across that window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Cell

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.pairing_cell_eq_zero
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P) (hZp : PerpItoIntegrals W ℱ hℱ Z)
    {V : Ω → ℂ} (hVm : Measurable V) {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, ‖V ω‖ ≤ Mv)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℂ _ (ℱ a) V)
    (hZV : ∫ ω, Z ω * V ω ∂P = 0) (l : ℝ) :
    ∫ ω, Z ω * V ω * Complex.exp (((l * (W.W b ω - W.W a ω) : ℝ) : ℂ) * Complex.I) ∂P = 0 := by sorry
