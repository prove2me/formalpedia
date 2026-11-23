-- Prove2me | Theorems.Thm_Kyprianou_Ch01_independentHeadMixesOneOffspring
-- name    : Kyprianou.Ch01.independentHeadMixesOneOffspring
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T19:00:25.312579+00:00
-- url     : https://prove2.me/theorems/324d4d10-cec6-47ef-9320-479eb7838e95
-- title:
--   Independent head mixes one offspring atom
-- statement:
--   Let $(A,M)$ be the first interarrival and the first mark, with joint law $\operatorname{Exp}(\lambda)\otimes\nu$ and independent of the shifted interarrivals and marks. Suppose the jump law charges the lattice point $j-1$ with mass $p_j$, and that the shifted population of height $y-1+j$ realises the kernel $K$ at every deterministic time. For $y\ge 1$, $t>0$, and a population size $k$, the atom
--   $$\{M=j-1\}\cap\{Y^{y-1+j}_{t-A/y}=k\}\cap\{A\le yt\}$$
--   then has probability
--   $$\int_0^{yt} f_\lambda(a)\,p_j\,K_{y-1+j}\!\left(t-\frac{a}{y},k\right)\,da,$$
--   where $f_\lambda$ is the exponential density of rate $\lambda$. The residual time $t-A/y$ is the branching-time coordinate after the first holding time.
-- source:
--   Kyprianou (2006), Section 1.3.4; one mark atom mixed against an independent shifted population kernel.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.independentHeadMixesOneOffspring
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
      ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ),
        exponentialPDFReal (rate : ℝ) a * (offspring j).toReal *
          (K ((y - 1) + j)
            (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal := by
  sorry
