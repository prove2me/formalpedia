-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstArrivalOneOffspringFromHeadTail
-- name    : Kyprianou.Ch01.reverseLampertiFirstArrivalOneOffspringFromHeadTail
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T18:46:50.492189+00:00
-- url     : https://prove2.me/theorems/3a4dab1a-bc2b-4ba8-bfe8-ac30cce67e30
-- title:
--   One offspring atom from the head-tail product
-- statement:
--   Let $\lambda>0$ and let the offspring law $(p_j)_{j\ge 0}$ be a probability on the nonnegative integers with $p_1=0$. Let the marks be supported on the lattice $\{j-1:j\in\mathbb{N}\}$, with
--   $$\nu(\{j-1\})=p_j.$$
--   Write $A$ for the first arrival time of the compound Poisson driver and $M$ for its first mark. Assume the following structural facts, which are not re-proved here:
--
--   - the pair $(A,M)$ has law $\operatorname{Exp}(\lambda)\otimes\nu$;
--   - the shifted interarrivals and marks are again a compound Poisson driver of rate $\lambda$ and jump law $\nu$;
--   - that head pair is independent of the shifted sequences;
--   - the whole interarrival-and-mark sequence has the infinite product law $\bigotimes_n\operatorname{Exp}(\lambda)\otimes\bigotimes_n\nu$.
--
--   Fix a height $y\ge 1$, a time $t>0$, a population size $k$, and one offspring index $j$. Let $K_z(s,k)$ be the probability that a population of height $z$, built from a driver of this law, has size $k$ at time $s$. Then the probability of the single atom
--   $$\{M=j-1\}\cap\{\text{the shifted population of height }y-1+j\text{ equals }k\text{ at time }t-A/y\}\cap\{A\le yt\}$$
--   equals the exponential integral of that one offspring mass:
--   $$\int_0^{yt}\lambda e^{-\lambda a}\,p_j\,K_{y-1+j}(t-a/y,\,k)\,da.$$
--   The residual clock $t-a/y$ is read in the branching-time coordinate, and the height $y-1+j$ is the height after the first mark $j-1$ is applied to the starting height $y$.
-- source:
--   Kyprianou (2006), Section 1.3.4; one mark atom of the first-arrival product law.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiFirstArrivalOneOffspringFromHeadTail
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
    (hHeadLaw : HasLaw (fun w => (arrival 0 w, marks 0 w))
      ((expMeasure rate).prod jumpLaw) Q)
    (hTailDriver : IsCompoundPoissonDriver
      (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w) rate jumpLaw Q)
    (hHeadTailIndependent : IndepFun
      (fun w => (arrival 0 w, marks 0 w))
      (fun w => ((fun n : ℕ => arrival (n + 1) w),
                 (fun n : ℕ => marks (n + 1) w))) Q)
    (hFullProductLaw : HasLaw
      (fun w (i : ℕ ⊕ ℕ) => (Sum.elim arrival marks i) w)
      (Measure.infinitePi
        (Sum.elim (fun _ : ℕ => expMeasure rate)
                  (fun _ : ℕ => jumpLaw))) Q)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0) (ht : 0 < t) (k j : ℕ) :
    (Q {ω |
        marks 0 ω = (j : ℝ) - 1 ∧
        (compoundPoissonToBranching
          (integerCompoundPoisson
            ((y - 1) + j)
            (fun n w => arrival (n + 1) w)
            (fun n w => marks (n + 1) w))
          (Real.toNNReal
            ((t : ℝ) - ProbabilityTheory.arrival arrival 0 ω / (y : ℝ)))
          ω).toNat = k ∧
        ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)}).toReal =
      ∫ a in (0 : ℝ)..(y : ℝ) * (t : ℝ),
        (rate : ℝ) * Real.exp (-((rate : ℝ) * a)) * (offspring j).toReal *
          (K ((y - 1) + j)
            (Real.toNNReal ((t : ℝ) - a / (y : ℝ))) k).toReal := by
  sorry
