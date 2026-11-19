-- Prove2me | Theorems.Thm_MeasureTheory_mul_upcrossingsBefore_le_sum_add_posPart
-- name    : MeasureTheory.mul_upcrossingsBefore_le_sum_add_posPart
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:37:49.681615+00:00
-- url     : https://prove2.me/theorems/f649db11-45b5-40fe-a7f0-a3fd26a1f1b0
-- title:
--   mul upcrossingsBefore le sum add posPart
-- statement:
--   The source theorem `MeasureTheory.mul_upcrossingsBefore_le_sum_add_posPart` is extracted from `BrownianMotion.Auxiliary.Upcrossing`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Probability.Martingale.Upcrossing

/-
Copyright (c) 2026 Rohit Manokaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran
-/

@[expose] public section

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω}
  {f g : ℕ → Ω → ℝ} {a b : ℝ} {N : ℕ} {ω : Ω}

theorem _root_.MeasureTheory.mul_upcrossingsBefore_le_sum_add_posPart (hab : a < b) :
    (b - a) * upcrossingsBefore a b f N ω ≤
      (∑ k ∈ Finset.range N, upcrossingStrat a b f N k ω * (f (k + 1) - f k) ω) + (a - f N ω)⁺ := by sorry
