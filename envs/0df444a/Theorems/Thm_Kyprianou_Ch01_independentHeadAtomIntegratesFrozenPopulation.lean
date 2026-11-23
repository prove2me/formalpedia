-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentHeadAtomIntegratesFrozenPopulation
-- name    : Kyprianou.Ch01.independentHeadAtomIntegratesFrozenPopulation
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T19:52:08.157897+00:00
-- url     : https://prove2.me/theorems/bbb0c67d-2da6-4733-8248-2661cffc91e6
-- title:
--   One offspring atom integrates the frozen population
-- statement:
--   Let $(A,M)$ be the first interarrival and the first mark, with joint law $\operatorname{Exp}(\lambda)\otimes\nu$ and independent of the shifted sequences. Fix $y\ge 1$, $t>0$, a population size $k$, and one offspring index $j$.
--
--   The atom
--   $$\{M=j-1\}\cap\{Y^{y-1+j}_{t-A/y}=k\}\cap\{A\le yt\}$$
--   has probability equal to the integral, over $(-\infty,yt]\times\{j-1\}$ in $\operatorname{Exp}(\lambda)\otimes\nu$, of the frozen probability
--   $$\mathbb{Q}\big(Y^{y-1+j}_{t-a/y}=k\big).$$
--   The time $t-a/y$ is deterministic once the arrival coordinate $a$ is fixed, and $Y$ is the branching population built from the shifted driver.
-- source:
--   Kyprianou (2006), Section 1.3.4; the first-arrival atom as an integral of frozen shifted populations.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.independentHeadAtomIntegratesFrozenPopulation
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
    (Q {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        arrival 0 ω ≤ (y : ℝ) * (t : ℝ)}).toReal =
      ∫ z in Iic ((y : ℝ) * (t : ℝ)) ×ˢ {((j : ℝ) - 1)},
        (Q {ω |
            (compoundPoissonToBranching
              (integerCompoundPoisson
                ((y - 1) + j)
                (fun n w => arrival (n + 1) w)
                (fun n w => marks (n + 1) w))
              (Real.toNNReal ((t : ℝ) - z.1 / (y : ℝ)))
              ω).toNat = k}).toReal
        ∂(expMeasure (rate : ℝ)).prod jumpLaw := by
  sorry
