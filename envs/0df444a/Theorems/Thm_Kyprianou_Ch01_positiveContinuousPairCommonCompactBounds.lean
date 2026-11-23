-- Prove2me | Theorems.Thm_Kyprianou_Ch01_positiveContinuousPairCommonCompactBounds
-- name    : Kyprianou.Ch01.positiveContinuousPairCommonCompactBounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:35:26.309634+00:00
-- url     : https://prove2.me/theorems/8b2d9ddb-b184-47d9-824c-6ad487c5fb8c
-- title:
--   Positive continuous pair of real trajectories has a common compact positive range
-- statement:
--   Two continuous positive real functions on finite closed time interval [0,T], T≥0, have a uniform common positive lower bound and finite upper bound. Apply isCompact_Icc.exists_isMinOn and exists_isMaxOn separately to both functions, then choose min of minima and max of maxima. A reusable step for moment-free branching cumulant ODE uniqueness.
-- source:
--   Mathlib extreme-value theorem, applied to positive branching cumulant trajectories in Kyprianou (2006) Chapter 1.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 Set Filter
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.positiveContinuousPairCommonCompactBounds
    (f g : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hfCont : ContinuousOn f (Set.Icc 0 T))
    (hgCont : ContinuousOn g (Set.Icc 0 T))
    (hfPos : ∀ t ∈ Set.Icc 0 T, 0 < f t)
    (hgPos : ∀ t ∈ Set.Icc 0 T, 0 < g t) :
    ∃ δ B : ℝ, 0 < δ ∧ δ ≤ B ∧
      (∀ t ∈ Set.Icc 0 T,
        f t ∈ Set.Icc δ B ∧ g t ∈ Set.Icc δ B) := by
  sorry
