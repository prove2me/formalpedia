-- Prove2me | Theorems.Thm_Kyprianou_Ch01_frozenKernelStronglyMeasurable
-- name    : Kyprianou.Ch01.frozenKernelStronglyMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T22:38:51.262806+00:00
-- url     : https://prove2.me/theorems/e68bd3af-bff0-457f-b102-f784d5bb730c
-- title:
--   Frozen population kernel is strongly measurable in the head
-- statement:
--   Let $(A,M)$ be the first interarrival and the first mark. Fix $y\ge 1$, $t>0$, a population size $k$, and one offspring index $j$.
--
--   The map
--   $$(a,m)\mapsto\mathbb{Q}(Y^{y-1+j}_{t-a/y}=k)$$
--   is almost everywhere strongly measurable with respect to the pushforward law of $(A,M)$.
-- source:
--   Kyprianou (2006), Section 1.3.4; the head pushforward integral is a preimage integral of the frozen kernel.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.frozenKernelStronglyMeasurable
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
    AEStronglyMeasurable
      (fun z : ℝ × ℝ =>
        (Q {ω |
            (compoundPoissonToBranching
              (integerCompoundPoisson
                ((y - 1) + j)
                (fun n w => arrival (n + 1) w)
                (fun n w => marks (n + 1) w))
              (Real.toNNReal ((t : ℝ) - z.1 / (y : ℝ)))
              ω).toNat = k}).toReal)
      (Q.map (fun w => (arrival 0 w, marks 0 w))) := by
  sorry
