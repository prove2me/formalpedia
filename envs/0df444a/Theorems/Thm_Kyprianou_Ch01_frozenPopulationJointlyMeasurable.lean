-- Prove2me | Theorems.Thm_Kyprianou_Ch01_frozenPopulationJointlyMeasurable
-- name    : Kyprianou.Ch01.frozenPopulationJointlyMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T23:20:51.392646+00:00
-- url     : https://prove2.me/theorems/1113a10e-4760-40b4-b712-e2e1835e84c4
-- title:
--   Frozen population is jointly measurable in outcome and clock
-- statement:
--   Let the shifted arrival and mark sequences drive the branching process. Fix $y\ge 1$, a population size $k$, and one offspring index $j$.
--
--   The joint event
--   $$\{(\omega,s):Y^{y-1+j}_s(\omega)=k\}\subseteq\Omega\times[0,\infty)$$
--   is measurable.
-- source:
--   Kyprianou (2006), Section 1.3.4; the clock dependence of the frozen probability is a slice of a joint event.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.frozenPopulationJointlyMeasurable
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
    MeasurableSet
      {p : Ω × ℝ≥0 |
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          p.2
          p.1).toNat = k} := by
  sorry
