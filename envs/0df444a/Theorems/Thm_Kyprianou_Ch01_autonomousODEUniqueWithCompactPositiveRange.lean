-- Prove2me | Theorems.Thm_Kyprianou_Ch01_autonomousODEUniqueWithCompactPositiveRange
-- name    : Kyprianou.Ch01.autonomousODEUniqueWithCompactPositiveRange
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T09:35:44.080004+00:00
-- url     : https://prove2.me/theorems/3ae778be-ee7a-43a7-b6e2-f79adaa0de5f
-- title:
--   ODE uniqueness on a finite interval when both trajectories stay in a common positive Lipschitz range
-- statement:
--   For two continuous real trajectories f,g in [δ,B]⊂(0,∞) on [0,T] satisfying the same right-derivative equation at every time before T and the same initial value, a uniform local Lipschitz estimate on v in [δ,B] gives f(T)=g(T). Use the exact Mathlib ODE_solution_unique_of_mem_Icc_right and LipschitzOnWith.of_dist_le_mul, with NNReal nonnegative Lipschitz constant. No stochastic or offspring assumptions.
-- source:
--   Pinned Mathlib Analysis.ODE.ExistUnique theorem ODE_solution_unique_of_mem_Icc_right; Kyprianou branching cumulant ODE, Chapter 1.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 Set Filter
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.autonomousODEUniqueWithCompactPositiveRange
    (v : ℝ → ℝ) (δ B C : ℝ) (hδ : 0 < δ)
    (hδB : δ ≤ B) (hC : 0 ≤ C)
    (hLip : ∀ x ∈ Set.Icc δ B, ∀ y ∈ Set.Icc δ B,
      |v y - v x| ≤ C * |y - x|)
    (f g : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hfCont : ContinuousOn f (Set.Icc 0 T))
    (hgCont : ContinuousOn g (Set.Icc 0 T))
    (hfRange : ∀ t ∈ Set.Icc 0 T, f t ∈ Set.Icc δ B)
    (hgRange : ∀ t ∈ Set.Icc 0 T, g t ∈ Set.Icc δ B)
    (hfDer : ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt f (v (f t)) (Set.Ici t) t)
    (hgDer : ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt g (v (g t)) (Set.Ici t) t)
    (hInit : f 0 = g 0) : f T = g T := by
  sorry
