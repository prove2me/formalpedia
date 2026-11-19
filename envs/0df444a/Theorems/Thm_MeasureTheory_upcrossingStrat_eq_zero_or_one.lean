-- Prove2me | Theorems.Thm_MeasureTheory_upcrossingStrat_eq_zero_or_one
-- name    : MeasureTheory.upcrossingStrat_eq_zero_or_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:37:37.245393+00:00
-- url     : https://prove2.me/theorems/a4385404-dcc6-4387-992a-57fdf1b0ebb0
-- title:
--   upcrossingStrat eq zero or one
-- statement:
--   The source theorem `MeasureTheory.upcrossingStrat_eq_zero_or_one` is extracted from `BrownianMotion.Auxiliary.Upcrossing`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F000

/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}

theorem _root_.MeasureTheory.upcrossingStrat_eq_zero_or_one (a b : ℝ) (f : ℕ → Ω → ℝ) (N n : ℕ) (ω : Ω) :
    upcrossingStrat a b f N n ω = 0 ∨ upcrossingStrat a b f N n ω = 1 := by sorry
