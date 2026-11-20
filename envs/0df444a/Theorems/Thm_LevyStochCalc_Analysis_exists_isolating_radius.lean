-- Prove2me | Theorems.Thm_LevyStochCalc_Analysis_exists_isolating_radius
-- name    : LevyStochCalc.Analysis.exists_isolating_radius
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:14:22.847676+00:00
-- url     : https://prove2.me/theorems/796dd0c3-8c73-4eff-a0b0-dee559c0cca4
-- title:
--   exists isolating radius
-- statement:
--   The source theorem asserting an isolating radius for a specified càdlàg jump.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_CadlagJumps_F000

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

theorem _root_.LevyStochCalc.Analysis.exists_isolating_radius {f : ℝ → ℝ}
    (hright : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∃ δ > 0, ∀ s ∈ Set.Ioo (t - δ) (t + δ), s ≠ t → |f s - Function.leftLim f s| < ε := by sorry
