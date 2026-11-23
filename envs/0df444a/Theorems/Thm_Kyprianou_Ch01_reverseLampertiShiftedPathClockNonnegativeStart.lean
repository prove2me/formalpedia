-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiShiftedPathClockNonnegativeStart
-- name    : Kyprianou.Ch01.reverseLampertiShiftedPathClockNonnegativeStart
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:02:25.520645+00:00
-- url     : https://prove2.me/theorems/df2ed400-6d6d-4228-8d40-ab56aa7c401d
-- title:
--   Reverse Lamperti clock-shift identity with nonnegative tail at restart
-- statement:
--   For deterministic integer paths X and Y, let X stay at the positive height y before physical time A and agree after A with Y shifted by A. If A is no later than physical time y*t and the shifted path is nonnegative at its initial time, the two stopped inverse-reciprocal-occupation populations agree at branching times t and t-A/y. Nonnegativity at the tail origin rules out the documented counterexample in the disproved source theorem: the first-negative-passage definition excludes negativity exactly at time zero. This replaces Kyprianou.Ch01.reverseLampertiShiftedPathClock, canonical UUID bcc2925f-f349-4e8e-bc7d-3dfa0df5a451, for the first-arrival decomposition, whose restarted integer compound-Poisson path starts from the nonnegative integer y-1+j. This theorem remains a genuine clock identity to prove, including occupation-clock translation, the strict right inverse and the shifted first-negative passage.
-- source:
--   Kyprianou (2006), Section 1.3.4, deterministic inverse-Lamperti time change at first-arrival restart; repaired after confirmed counterexample to initial-time negativity on 23 November 2026.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiShiftedPathClockNonnegativeStart
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω) :
    (compoundPoissonToBranching X t ω).toNat =
      (compoundPoissonToBranching Y
        (Real.toNNReal ((t : ℝ) - A / (y : ℝ))) ω).toNat := by
  sorry
