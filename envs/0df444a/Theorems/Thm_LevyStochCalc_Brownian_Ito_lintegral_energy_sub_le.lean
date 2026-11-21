-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_sub_le
-- name    : LevyStochCalc.Brownian.Ito.lintegral_energy_sub_le
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:01:21.228437+00:00
-- url     : https://prove2.me/theorems/a8bf7c3e-a6bf-4da2-97ed-f384235cf7fc
-- title:
--   lintegral energy sub le
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.lintegral_energy_sub_le` is extracted from `LevyStochCalc.Ito.VectorItoVersionSup`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_VectorItoProcessDiff_F000
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F003

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

omit [IsProbabilityMeasure P] in

theorem _root_.LevyStochCalc.Brownian.Ito.lintegral_energy_sub_le {f g h : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hh : Measurable (Function.uncurry h)) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s - g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖f ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖g ω s - h ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by sorry
