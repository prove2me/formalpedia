-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiFirstJumpRestartIntegral
-- name    : Kyprianou.Ch01.reverseLampertiFirstJumpRestartIntegral
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T13:33:46.427801+00:00
-- url     : https://prove2.me/theorems/b2596eb1-4cb5-4970-94a3-4ada127bb02a
-- title:
--   First-jump contribution as a restarted integral
-- statement:
--   Fix $y\ge 1$, $t>0$, and a state $k\in\mathbb{N}$. On the event $\tau_1\le yt$ the first jump of the driving compound Poisson process has rung by branching time $t$. The strong Markov property at that jump restarts an independent copy of the reverse Lamperti population from the post-jump height $y-1+J$, with residual branching time $t-s$, where $s=\tau_1/y$ is the branching time of the first arrival and $J$ is drawn from the offspring law $(p_j)_{j\ge 0}$.
--
--   Integrating the exponential density of $\tau_1$ therefore gives
--   $$\mathbb{Q}\big(Y^y_t=k,\;\tau_1\le yt\big)=\int_0^t \lambda y\, e^{-\lambda y s}\sum_{j=0}^\infty p_j\, K(y-1+j,(t-s)_+)(k)\,ds,$$
--   and the integrand is interval-integrable on $[0,t]$. Here $(t-s)_+=\max(t-s,0)$, which equals $t-s$ throughout the interval of integration.
-- source:
--   A. E. Kyprianou, Fluctuations of Levy Processes with Applications, 2nd ed., Springer, Chapter 1, reverse Lamperti representation and the branching property.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiFirstJumpRestartIntegral
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
    IntervalIntegrable
        (fun s : ℝ =>
          ((rate : ℝ) * (y : ℝ)) * Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
        volume 0 (t : ℝ) ∧
      (Q {ω |
          (compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks) t ω).toNat = k ∧
          ¬ ((y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω)}).toReal =
        ∫ s in (0 : ℝ)..(t : ℝ),
          ((rate : ℝ) * (y : ℝ)) * Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal := by
  sorry
