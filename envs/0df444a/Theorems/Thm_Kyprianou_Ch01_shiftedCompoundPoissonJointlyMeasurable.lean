-- Prove2me | Theorems.Thm_Kyprianou_Ch01_shiftedCompoundPoissonJointlyMeasurable
-- name    : Kyprianou.Ch01.shiftedCompoundPoissonJointlyMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T23:45:06.023818+00:00
-- url     : https://prove2.me/theorems/87695116-7354-4bdb-a945-a18959991f89
-- title:
--   Shifted compound Poisson is jointly measurable in outcome and time
-- statement:
--   Let the shifted arrival and mark sequences drive a real compound-Poisson path.
--
--   The map
--   $$(\omega,u)\mapsto\xi_u(\omega)$$
--   is measurable as a function $\Omega\times[0,\infty)\to\mathbb{R}$.
-- source:
--   Kyprianou (2006), Section 1.3.4; the lattice walk is the floor of a constant plus the real path.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.shiftedCompoundPoissonJointlyMeasurable
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
        ProbabilityTheory.compoundPoisson 0
          (fun n w => arrival (n + 1) w)
          (fun n w => marks (n + 1) w)
          (p.2 : ℝ)
          p.1) := by
  sorry
