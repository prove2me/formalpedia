-- Prove2me | Theorems.Thm_Kyprianou_Ch01_frozenArrivalKernelStronglyMeasurable
-- name    : Kyprianou.Ch01.frozenArrivalKernelStronglyMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T22:46:57.992871+00:00
-- url     : https://prove2.me/theorems/a0ba5dec-a2e2-4684-b0f4-5c2e29ed68b6
-- title:
--   Frozen arrival kernel is strongly measurable
-- statement:
--   Let $(A,M)$ be the first interarrival and the first mark. Fix $y\ge 1$, $t>0$, a population size $k$, and one offspring index $j$.
--
--   The real function
--   $$a\mapsto\mathbb{Q}(Y^{y-1+j}_{t-a/y}=k)$$
--   is strongly measurable.
-- source:
--   Kyprianou (2006), Section 1.3.4; the frozen kernel depends on the head only through the arrival time.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.frozenArrivalKernelStronglyMeasurable
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
      (fun a : ℝ =>
        (Q {ω |
            (compoundPoissonToBranching
              (integerCompoundPoisson
                ((y - 1) + j)
                (fun n w => arrival (n + 1) w)
                (fun n w => marks (n + 1) w))
              (Real.toNNReal ((t : ℝ) - a / (y : ℝ)))
              ω).toNat = k}).toReal) := by
  sorry
