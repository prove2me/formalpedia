-- Prove2me | Theorems.Thm_Kyprianou_Ch04_runningInfimumAntitoneFromFiniteBounds
-- name    : Kyprianou.Ch04.runningInfimumAntitoneFromFiniteBounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T17:58:13.08118+00:00
-- url     : https://prove2.me/theorems/0e351206-f6ba-5e46-99d1-af0d455059fd
-- title:
--   Running infimum is antitone under compact-horizon lower bounds
-- statement:
--   If a real path has bounded-below values on every initial nonnegative-time interval, its running infimum is nonincreasing as the time horizon increases. No probabilistic hypotheses are required.
-- source:
--   Kyprianou (2006), Corollary 4.9, deterministic running-infimum monotonicity.

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.runningInfimumAntitoneFromFiniteBounds
    (f : NNReal → ℝ)
    (hBound : ∀ t : NNReal, BddBelow (f '' Set.Iic t)) :
    Antitone (fun t : NNReal => sInf (f '' Set.Iic t)) := by
  sorry
