-- Prove2me | Theorems.Thm_Kyprianou_Ch01_jumpCountLocalRightConstOfRegularArrival
-- name    : Kyprianou.Ch01.jumpCountLocalRightConstOfRegularArrival
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:42:41.679501+00:00
-- url     : https://prove2.me/theorems/5d388754-1819-4644-a607-37e76b62600d
-- title:
--   Local right constancy of the source compound-Poisson jump count
-- statement:
--   For any strictly increasing sequence of real-valued arrival times tending to infinity, the source jumpCount T function is constant immediately to the right of every nonnegative observation time. The interval can be taken from time t to the next arrival T(jumpCount T t), which lies strictly above t, then converted to an NNReal endpoint. Use the two already public LevyFoundations jump-count results jumpCountMonotone and jumpCountLtIff, whose jump-count definition is exactly Nat.sInf {n | t<T n}. Prove the interval count bounds and construct the right-neighbourhood. This isolates the deterministic step-function argument needed for integer compound Poisson right-continuity without private theorem imports.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4. Supports Open original rightcontinuity child 89e2d356-663a-425c-afcd-ad3841267c58 of stopped Lamperti driver path. Public lemmas levy_foundations_jumpCountMonotone UUID 0f857a2f-c372-4dce-894f-806cfb7c199b and levy_foundations_jumpCountLtIff UUID 64a78fc4-e895-4dc6-8a16-7be00891d854; exact source ProbabilityTheory.jumpCount in Definitions.Def_LeanLevy_Processes_PiecewisePath.

import Mathlib
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.jumpCountLocalRightConstOfRegularArrival
    (T : ℕ → ℝ) (hmono : StrictMono T)
    (htop : Tendsto T atTop atTop) (t : ℝ≥0) :
    ∃ c : ℝ≥0, t < c ∧
      ∀ s ∈ Set.Ico t c,
        ProbabilityTheory.jumpCount T (s : ℝ) =
        ProbabilityTheory.jumpCount T (t : ℝ) := by
  sorry
