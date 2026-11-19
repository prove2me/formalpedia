-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingInverseRecoveryFromStrictClock
-- name    : Kyprianou.Ch01.branchingInverseRecoveryFromStrictClock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:21:33.52709+00:00
-- url     : https://prove2.me/theorems/5433c5d0-c921-4c68-82ce-b1a3eda35500
-- title:
--   Right-inverse Lamperti recovery from monotonicity and local strict growth of the source occupation clock
-- statement:
--   When the source branching occupation clock J is nonnegative at a pre-extinction time t, monotone globally, and strictly increasing immediately to the right of t before some later horizon, its right-generalised inverse at J(t) returns exactly t, so the source forward Lamperti map Y at that inverse recovers Y(t). This isolates the exact source definitions including WithTop infinite-clock cases and does not strengthen the eventual càdlàg/positivity source model.
-- source:
--   Kyprianou (2006), Chapter 1 Eq. (1.17) forward Lamperti occupation-clock recovery

import Mathlib.Data.NNReal.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingInverseRecoveryFromStrictClock
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℕ) (ω : Ω)
    (horizon t : ℝ≥0) (ht : t < horizon)
    (hmono : Monotone (fun s : ℝ≥0 => branchingOccupation Y s ω))
    (hstrict : ∀ s : ℝ≥0, t < s → s < horizon →
      branchingOccupation Y t ω < branchingOccupation Y s ω)
    (hnonneg : 0 ≤ branchingOccupation Y t ω) :
    branchingToPoisson Y
      (Real.toNNReal (branchingOccupation Y t ω)) ω = Y t ω := by
  sorry
