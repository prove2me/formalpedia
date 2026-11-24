-- Prove2me | Theorems.Thm_Kyprianou_Ch01_shiftedLatticeWalkJointlyMeasurable
-- name    : Kyprianou.Ch01.shiftedLatticeWalkJointlyMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T23:39:36.657997+00:00
-- url     : https://prove2.me/theorems/826019d7-215e-4c56-b83b-75f7a47ca402
-- title:
--   Shifted lattice walk is jointly measurable in outcome and time
-- statement:
--   Let the shifted arrival and mark sequences drive a lattice compound-Poisson walk from height $y-1+j$.
--
--   The map
--   $$(\omega,u)\mapsto X_u(\omega)$$
--   is measurable as a function $\Omega\times[0,\infty)\to\mathbb{Z}$.
-- source:
--   Kyprianou (2006), Section 1.3.4; the frozen population is the Lamperti image of the shifted lattice walk.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.shiftedLatticeWalkJointlyMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hHeadLaw : HasLaw (fun w => (arrival 0 w, marks 0 w))
      ((expMeasure rate).prod jumpLaw) Q)
    (hHeadTailIndependent : IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k j : ℕ) :
    Measurable
      (fun p : Ω × ℝ≥0 =>
        integerCompoundPoisson
          ((y - 1) + j)
          (fun n w => arrival (n + 1) w)
          (fun n w => marks (n + 1) w)
          p.2
          p.1) := by
  sorry
