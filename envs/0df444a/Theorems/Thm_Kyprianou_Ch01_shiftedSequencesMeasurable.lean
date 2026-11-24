-- Prove2me | Theorems.Thm_Kyprianou_Ch01_shiftedSequencesMeasurable
-- name    : Kyprianou.Ch01.shiftedSequencesMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T23:50:44.982374+00:00
-- url     : https://prove2.me/theorems/ee75d6b8-b670-442c-a8ae-a2c89c28ffc9
-- title:
--   Shifted arrival and mark sequences are measurable
-- statement:
--   Let $(A,M)$ be the first interarrival and the first mark, with the stated law and independence from the shifted sequences.
--
--   For every index $n$, the shifted interarrival $\tau_{n+1}$ and the shifted mark $Y_{n+1}$ are measurable functions of $\omega$.
-- source:
--   Kyprianou (2006), Section 1.3.4; the real path is measurable once the driver sequences are.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.shiftedSequencesMeasurable
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
    (∀ n : ℕ, Measurable (fun w => arrival (n + 1) w)) ∧
      ∀ n : ℕ, Measurable (fun w => marks (n + 1) w) := by
  sorry
