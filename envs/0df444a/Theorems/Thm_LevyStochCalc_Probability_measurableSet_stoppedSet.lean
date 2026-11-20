-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_measurableSet_stoppedSet
-- name    : LevyStochCalc.Probability.measurableSet_stoppedSet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:30:37.567314+00:00
-- url     : https://prove2.me/theorems/8fc8e67c-fd68-476c-86f6-2497e899b8c0
-- title:
--   measurableSet stoppedSet
-- statement:
--   The source theorem `LevyStochCalc.Probability.measurableSet_stoppedSet` is extracted from `LevyStochCalc.Probability.StoppedProgressive`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a progressively measurable process

Cutting a process off at a stopping time keeps it progressively measurable: before a time `t` the
region `{(ω, s) : s ≤ t, s ≤ τ ω}` is the complement, inside `Ω × (-∞, t]`, of a countable union
of rectangles `{τ ≤ q} × (q, t]` over the rationals, each measurable for the σ-algebra at `t`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem _root_.LevyStochCalc.Probability.measurableSet_stoppedSet {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) : MeasurableSet (stoppedSet τ) := by sorry
