-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalPoissonClockMixture
-- name    : Kyprianou.Ch01.reverseLampertiFirstArrivalPoissonClockMixture
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T17:42:43.446378+00:00
-- url     : https://prove2.me/theorems/4e0f086a-4814-4597-a306-2726e027c148
-- title:
--   First-arrival mixture on the Poisson clock
-- statement:
--   Let $A$ be the first arrival time of a compound Poisson driver of rate $\lambda>0$, and let the mark of that jump determine an offspring count $j$ with mass $p_j$. On the event $A\le y t$, restart the integer-valued path from height $y-1+j$ using only the later arrivals and marks, and read the reverse Lamperti population at residual time $t-A/y$.
--
--   The mass of the event that this restarted population equals $k$ is the mixture
--   $$\int_0^{yt} \lambda e^{-\lambda a}\sum_{j\ge 0} p_j\, K_{y-1+j}(t-a/y,\, k)\, da.$$
--
--   The exponential density is the law of $A$. The kernel $K$ is the population law of a fresh driver, evaluated at the branching-time residual $t-a/y$.
-- source:
--   Kyprianou (2006), Section 1.3.4; first-event mixture of the nonexplosive inverse Lamperti law, before the branching-time substitution a = y s.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiFirstArrivalPoissonClockMixture
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    (Q { ω |
          (compoundPoissonToBranching
            (integerCompoundPoisson
              ((y - 1) +
                (Int.floor (marks 0 ω + 1)).toNat)
              (fun n w => arrival (n + 1) w)
              (fun n w => marks (n + 1) w))
            (Real.toNNReal
              ((t : ℝ) -
                ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
            ω).toNat = k ∧
          ¬ ((y : ℝ) * (t : ℝ) <
          ProbabilityTheory.arrival arrival 0 ω) }).toReal =
        ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ),
          (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j)
                (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal := by
  sorry
