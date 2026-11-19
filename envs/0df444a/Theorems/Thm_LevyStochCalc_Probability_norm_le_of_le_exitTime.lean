-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_norm_le_of_le_exitTime
-- name    : LevyStochCalc.Probability.norm_le_of_le_exitTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:34:06.156526+00:00
-- url     : https://prove2.me/theorems/aa8d5a94-8b79-421d-b5e6-7cbd461071e6
-- title:
--   norm le of le exitTime
-- statement:
--   The source theorem `LevyStochCalc.Probability.norm_le_of_le_exitTime` is extracted from `LevyStochCalc.Probability.ExitTime`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ExitTime_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exit times of a process with continuous paths

`exitTime X k ω` is the first nonnegative time at which the path `X ω` has norm at least `k`, and
`⊤` when the path never reaches that norm. For continuous paths the comparison `exitTime X k ω ≤ t`
is decided by the values of the path on the rationals of `[0, t]`, so the exit time is a stopping
time for any filtration the process is adapted to. Letting `k` grow gives a localising sequence:
every time lies strictly below `exitTime X k` for all large `k`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]

theorem _root_.LevyStochCalc.Probability.norm_le_of_le_exitTime {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {k s : ℝ}
    (hs : 0 < s) (hle : (s : WithTop ℝ) ≤ exitTime X k ω) : ‖X ω s‖ ≤ k := by sorry
