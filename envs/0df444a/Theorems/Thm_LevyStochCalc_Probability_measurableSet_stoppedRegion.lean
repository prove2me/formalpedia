-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_measurableSet_stoppedRegion
-- name    : LevyStochCalc.Probability.measurableSet_stoppedRegion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:29:33.868566+00:00
-- url     : https://prove2.me/theorems/b0b75ad5-6151-49af-b974-159943a06183
-- title:
--   measurableSet stoppedRegion
-- statement:
--   The source theorem `LevyStochCalc.Probability.measurableSet_stoppedRegion` is extracted from `LevyStochCalc.Probability.StoppedProgressive`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F000

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

theorem _root_.LevyStochCalc.Probability.measurableSet_stoppedRegion {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (t : ℝ) :
    MeasurableSet[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance] (stoppedRegion τ t) := by sorry
