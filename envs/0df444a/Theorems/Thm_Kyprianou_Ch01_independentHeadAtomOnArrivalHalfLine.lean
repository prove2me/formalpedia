-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentHeadAtomOnArrivalHalfLine
-- name    : Kyprianou.Ch01.independentHeadAtomOnArrivalHalfLine
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T19:44:28.979844+00:00
-- url     : https://prove2.me/theorems/2d036d91-765d-41e9-ae61-e987517de371
-- title:
--   One offspring atom on the arrival half-line
-- statement:
--   Let $(A,M)$ be the first interarrival and the first mark, with joint law $\operatorname{Exp}(\lambda)\otimes\nu$ and independent of the shifted sequences. Suppose the shifted population of height $y-1+j$ realises the kernel $K$ at every deterministic time.
--
--   For $y\ge 1$, $t>0$, and a population size $k$, the atom
--   $$\{M=j-1\}\cap\{Y^{y-1+j}_{t-A/y}=k\}\cap\{A\le yt\}$$
--   has probability equal to the integral of $K_{y-1+j}(t-a/y,k)$ over $(-\infty,yt]\times\{j-1\}$ in $\operatorname{Exp}(\lambda)\otimes\nu$. The kernel is read at the residual branching time $t-a/y$.
-- source:
--   Kyprianou (2006), Section 1.3.4; the first-arrival atom integrated on the half-line up to the branching time.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.independentHeadAtomOnArrivalHalfLine
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
    (K : PopulationLaws)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k j : ℕ)
    (hPop : ∀ s : ℝ≥0,
      Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w)) s ω).toNat = k} =
        K ((y - 1) + j) s k) :
    (Q {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal ((t : ℝ) - arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < arrival 0 ω)}).toReal =
      ∫ z in Iic ((y : ℝ) * (t : ℝ)) ×ˢ {((j : ℝ) - 1)},
        (K ((y - 1) + j)
          (Real.toNNReal ((t : ℝ) - z.1 / (y : ℝ))) k).toReal
        ∂(expMeasure (rate : ℝ)).prod jumpLaw := by
  sorry
