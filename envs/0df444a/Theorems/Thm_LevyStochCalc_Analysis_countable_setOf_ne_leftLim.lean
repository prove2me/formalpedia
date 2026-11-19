-- Prove2me | Theorems.Thm_LevyStochCalc_Analysis_countable_setOf_ne_leftLim
-- name    : LevyStochCalc.Analysis.countable_setOf_ne_leftLim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:14:32.613359+00:00
-- url     : https://prove2.me/theorems/336f31c7-7cd7-41fc-b7f0-0f7145cc33ae
-- title:
--   countable setOf ne leftLim
-- statement:
--   The source theorem `LevyStochCalc.Analysis.countable_setOf_ne_leftLim` is extracted from `LevyStochCalc.Analysis.CadlagJumps`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jumps of a càdlàg function

A function on the line that is right-continuous and has left limits everywhere jumps only at
isolated points of each level of the jump size, so its jump set is countable and therefore
Lebesgue-null: such a function agrees with its left limits almost everywhere.
-/

open Filter Set MeasureTheory
open scoped Topology

namespace LevyStochCalc.Analysis

theorem _root_.LevyStochCalc.Analysis.countable_setOf_ne_leftLim {f : ℝ → ℝ}
    (hright : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) :
    {t : ℝ | f t ≠ Function.leftLim f t}.Countable := by sorry
