-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_predictableDyadicSimple_brownian_eval_bounded
-- name    : LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_eval_bounded
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T09:27:56.612466+00:00
-- url     : https://prove2.me/theorems/b189f453-d26e-4bee-b5f8-df408e797f89
-- title:
--   predictableDyadicSimple brownian eval bounded
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_eval_bounded` is extracted from `LevyStochCalc.Brownian.ItoDensityShiftedAverages`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityShiftedAverages_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Left-shifted dyadic averages and cell-average identities

The left-shifted dyadic cell averages, which on the interval `(t_{i-1}, t_i]` take the
average over the previous cell and are therefore adapted, the simple predictable process
they define, and the identification of a cell average with an average of the integrand
over a closed ball, through the dyadic index of a time `s ∈ (0, T]`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- `omit` the unused `[MeasurableSpace Ω]` section variable.

theorem _root_.LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_eval_bounded
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) (s : ℝ) (ω : Ω) :
    |(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω|
      ≤ max M 0 := by sorry
