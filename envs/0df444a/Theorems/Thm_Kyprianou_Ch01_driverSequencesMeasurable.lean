-- Prove2me | Theorems.Thm_Kyprianou_Ch01_driverSequencesMeasurable
-- name    : Kyprianou.Ch01.driverSequencesMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T01:44:00.606971+00:00
-- url     : https://prove2.me/theorems/e7f02e5c-b52c-4f3e-b1ea-98c94ec2f433
-- title:
--   Driver arrival and mark sequences are measurable
-- statement:
--   Let $(A,M)$ be the first interarrival and the first mark, with the stated law and independence from the shifted sequences.
--
--   For every index $n$, the interarrival $\tau_n$ and the mark $Y_n$ are measurable functions of $\omega$.
-- source:
--   Kyprianou (2006), Section 1.3.4; shifted measurability is the successor case of driver measurability.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.driverSequencesMeasurable
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
    (∀ n : ℕ, Measurable (arrival n)) ∧
      ∀ n : ℕ, Measurable (marks n) := by
  sorry
