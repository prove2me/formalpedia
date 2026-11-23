-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentHeadAtomHasExponentialMass
-- name    : Kyprianou.Ch01.independentHeadAtomHasExponentialMass
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T19:23:57.588362+00:00
-- url     : https://prove2.me/theorems/34e8df08-5e3a-4d48-844b-2e51fab15910
-- title:
--   One offspring atom has exponential mass
-- statement:
--   Let $(A,M)$ be the first interarrival and the first mark, with joint law $\operatorname{Exp}(\lambda)\otimes\nu$ and independent of the shifted interarrival and mark sequences. Suppose $\nu(\{j-1\})=p_j$, and that the shifted population of height $y-1+j$ realises the kernel $K$ at every deterministic time.
--
--   For $y\ge 1$, $t>0$, and a population size $k$, the atom
--   $$\{M=j-1\}\cap\{Y^{y-1+j}_{t-A/y}=k\}\cap\{A\le yt\}$$
--   then has probability equal to the integral of $p_j\,K_{y-1+j}(t-a/y,k)$ against the exponential law of rate $\lambda$, taken over the interval $(0,yt]$. The residual time $t-A/y$ is the branching-time coordinate after the first holding time.
-- source:
--   Kyprianou (2006), Section 1.3.4; the first-arrival atom integrated against the exponential law.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.independentHeadAtomHasExponentialMass
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
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
      ∫ a in Ioc (0 : ℝ) ((y : ℝ) * (t : ℝ)),
        (offspring j).toReal *
          (K ((y - 1) + j)
            (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal
          ∂expMeasure (rate : ℝ) := by
  sorry
