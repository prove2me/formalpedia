-- Prove2me | Theorems.Thm_Kyprianou_Ch01_frozenTimeKernelStronglyMeasurable
-- name    : Kyprianou.Ch01.frozenTimeKernelStronglyMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T22:56:33.186278+00:00
-- url     : https://prove2.me/theorems/798cbbea-1013-474c-8089-9110dfb19f31
-- title:
--   Frozen kernel is strongly measurable in the branching clock
-- statement:
--   Let the shifted arrival and mark sequences drive the branching process. Fix $y\ge 1$, $t>0$, a population size $k$, and one offspring index $j$.
--
--   The function
--   $$s\mapsto\mathbb{Q}(Y^{y-1+j}_s=k)$$
--   is strongly measurable in the branching clock $s\in[0,\infty)$.
-- source:
--   Kyprianou (2006), Section 1.3.4; the arrival time enters the frozen kernel through a continuous clock.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.frozenTimeKernelStronglyMeasurable
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
    StronglyMeasurable
      (fun s : ℝ≥0 =>
        (Q {ω |
            (compoundPoissonToBranching
              (integerCompoundPoisson
                ((y - 1) + j)
                (fun n w => arrival (n + 1) w)
                (fun n w => marks (n + 1) w))
              s
              ω).toNat = k}).toReal) := by
  sorry
