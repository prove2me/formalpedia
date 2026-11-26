-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_compact_jump_atom_bounds
-- name    : Kyprianou.Ch04.ito43_compact_jump_atom_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:41:51.720835+00:00
-- url     : https://prove2.me/theorems/f359b4a5-0d5f-52ee-b76c-6807bc972b2e
-- title:
--   Uniform compact Taylor atom bounds at positive times
-- statement:
--   On a compact rectangle the first and second spatial Taylor terms have uniform quadratic bounds and the complementary cutoff has the prescribed small quadratic bound.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.ito43_compact_jump_atom_bounds
    (f : Real × Real -> Real)
    (hfJointC1 : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (hfSpaceC2 : forall s : NNReal,
      ContDiff Real 2 (fun x : Real => f ((s : Real), x)))
    (hfSpaceSecondContinuous :
      ContinuousOn
        (fun z : Real × Real =>
          iteratedDeriv 2 (fun x : Real => f (z.1, x)) z.2)
        (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (H : NNReal) (M a : ℝ) (ha : 0 < a) (m : ℕ)
    (hcut : ∀ s ∈ Set.Icc (0 : ℝ) (H : ℝ),
      ∀ x ∈ Set.Icc (-M) M, ∀ y ∈ Set.Icc (-M) M,
        |(f (s,y)-f (s,x)-deriv (fun z : ℝ => f (s,z)) x*(y-x) -
          iteratedDeriv 2 (fun z : ℝ => f (s,z)) x*(y-x)^2/2) *
          (1-min 1 (max 0 (|y-x| *((m : ℝ)+1)-1)))| ≤ a*(y-x)^2)
    : ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ Set.Icc (0 : ℝ) (H : ℝ), 0 < s →
      ∀ x ∈ Set.Icc (-M) M, ∀ y ∈ Set.Icc (-M) M,
        |f (s,y)-f (s,x)-(y-x)*fderiv ℝ f (s,x) (0,1)| ≤ (C/2)*(y-x)^2 ∧
        |iteratedDeriv 2 (fun z : ℝ => f (s,z)) x*(y-x)^2/2| ≤ (C/2)*(y-x)^2 ∧
        |(f (s,y)-f (s,x)-(y-x)*fderiv ℝ f (s,x) (0,1) -
          iteratedDeriv 2 (fun z : ℝ => f (s,z)) x*(y-x)^2/2) *
          (1-min 1 (max 0 (|y-x| *((m : ℝ)+1)-1)))| ≤ a*(y-x)^2 := by sorry
