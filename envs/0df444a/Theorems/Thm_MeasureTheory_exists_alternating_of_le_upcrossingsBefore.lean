-- Prove2me | Theorems.Thm_MeasureTheory_exists_alternating_of_le_upcrossingsBefore
-- name    : MeasureTheory.exists_alternating_of_le_upcrossingsBefore
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:38:42.804565+00:00
-- url     : https://prove2.me/theorems/96fa852f-5348-4222-a8e9-6cb0e4e3bae4
-- title:
--   exists alternating of le upcrossingsBefore
-- statement:
--   The source theorem `MeasureTheory.exists_alternating_of_le_upcrossingsBefore` is extracted from `BrownianMotion.Auxiliary.Upcrossing`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.MeasureTheory.exists_alternating_of_le_upcrossingsBefore (hab : a < b) {m : ℕ}
    (hm : m ≤ upcrossingsBefore a b f N ω) :
    ∃ c : ℕ → ℕ, (∀ i, i + 1 < 2 * m → c i < c (i + 1)) ∧ (∀ i < 2 * m, c i < N)
      ∧ (∀ i < m, f (c (2 * i)) ω ≤ a) ∧ (∀ i < m, b ≤ f (c (2 * i + 1)) ω) := by sorry
