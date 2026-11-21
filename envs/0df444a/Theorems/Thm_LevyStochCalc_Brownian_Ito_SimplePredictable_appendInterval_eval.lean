-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_appendInterval_eval
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.appendInterval_eval
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T15:57:07.25978+00:00
-- url     : https://prove2.me/theorems/f23decb5-f764-410e-9474-8edf4e03f9bc
-- title:
--   appendInterval eval
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.SimplePredictable.appendInterval_eval` is extracted from `LevyStochCalc.Brownian.SimplePredictableRefineAppend`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineAppend_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Zero-extension of a simple predictable to a larger horizon

Appending one interval carrying the coefficient `0`
(`SimplePredictable.appendInterval`) turns a `SimplePredictable Ω T` into a
`SimplePredictable Ω T'` on a larger horizon with the same `eval`, the same
simple integral and the same adaptedness, so that two approximants on different
horizons can be compared on a common endpoint.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.SimplePredictable.appendInterval_eval
    {T : ℝ} (H : SimplePredictable Ω T) {T' : ℝ}
    (hlt : H.partition (Fin.last H.N) < T') (s : ℝ) (ω : Ω) :
    (H.appendInterval hlt).eval s ω = H.eval s ω := by sorry
