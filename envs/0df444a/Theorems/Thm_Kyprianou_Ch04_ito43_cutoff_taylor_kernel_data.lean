-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_taylor_kernel_data
-- name    : Kyprianou.Ch04.ito43_cutoff_taylor_kernel_data
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:46:15.350257+00:00
-- url     : https://prove2.me/theorems/8f59817d-6649-5e56-8ab2-a52047289ec1
-- title:
--   Continuous spatial Taylor cutoff kernel
-- statement:
--   The joint spatial slice derivatives are continuous on nonnegative times, including time zero by differentiation within the closed half-plane. The explicit continuous cutoff makes the kernel zero near the origin.
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
open scoped Topology

theorem Kyprianou.Ch04.ito43_cutoff_taylor_kernel_data (f : Real × Real -> Real)
    (hfJointC1 : ContDiffOn Real 1 f
      (Set.prod (Set.Ici (0 : Real)) Set.univ))
    (hfSpaceC2 : forall s : NNReal,
      ContDiff Real 2 (fun x : Real => f ((s : Real), x)))
    (hfSpaceSecondContinuous :
      ContinuousOn
        (fun z : Real × Real =>
          iteratedDeriv 2 (fun x : Real => f (z.1, x)) z.2)
        (Set.prod (Set.Ici (0 : Real)) Set.univ)) :
    ∀ m : ℕ,
    let K : NNReal → ℝ → ℝ → ℝ := fun s x z =>
      (f ((s : ℝ),x+z) - f ((s : ℝ),x) -
        deriv (fun y : ℝ => f ((s : ℝ),y)) x*z -
        iteratedDeriv 2 (fun y : ℝ => f ((s : ℝ),y)) x*z^2/2) *
      min 1 (max 0 (|z| * ((m : ℝ)+1)-1))
    Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2) ∧
      ∀ s x z, |z| ≤ 1/((m:ℝ)+1) → K s x z = 0 := by sorry
