-- Prove2me | Theorems.Thm_Kyprianou_Ch01_passageLaplaceAntitoneStoppingTime
-- name    : Kyprianou.Ch01.passageLaplaceAntitoneStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:07:01.562222+00:00
-- url     : https://prove2.me/theorems/fd517bb3-97fd-4e48-a819-99a3b7007501
-- title:
--   Discounted first passage Laplace payoff is antitone in extended stopping time
-- statement:
--   For any nonnegative discount rate and pathwise ordered extended nonnegative stopping times T≤U, the original passageLaplace payoff, which is zero at infinity and exp(-q t) at finite time, decreases with the stopping time. All WithTop cases, including non-hitting trajectories, are respected.
-- source:
--   Kyprianou 2006 Ch1 Exercise 1.10, deterministic discounted passage-time monotonicity needed for zero-barrier recovery.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.passageLaplaceAntitoneStoppingTime
    {Ω : Type*} [MeasurableSpace Ω]
    (T U : Ω → WithTop ℝ≥0) (q : ℝ) (hq : 0 ≤ q)
    (hle : ∀ ω, T ω ≤ U ω) (ω : Ω) :
    passageLaplace U q ω ≤ passageLaplace T q ω := by
  sorry
