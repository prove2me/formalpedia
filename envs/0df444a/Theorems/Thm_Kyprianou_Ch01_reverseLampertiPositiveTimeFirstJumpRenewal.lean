-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiPositiveTimeFirstJumpRenewal
-- name    : Kyprianou.Ch01.reverseLampertiPositiveTimeFirstJumpRenewal
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T13:20:31.301941+00:00
-- url     : https://prove2.me/theorems/b7029cc8-2a47-40d1-bbe1-3a05d8fa1311
-- title:
--   First-jump renewal equation for the nonexplosive reverse Lamperti population
-- statement:
--   Let $K_y(t)$ be the law of the reverse Lamperti population started from $y$ individuals, built from the integer compound-Poisson driver of rate $\lambda>0$ with offspring jump sizes $k-1$, under the stated reciprocal-clock non-explosion. Extinction is absorbing: $K_0(t)=\delta_0$ for every $t$. For every $y\ge 1$, every $t>0$, and every state $k$, the first-step formula holds. The probability of still sitting at $y$ with no jump is $e^{-\lambda y t}$. Otherwise the first branching event has density $\lambda y e^{-\lambda y s}$ on $(0,t)$, replaces one individual by $j$ offspring with probability $p_j$ (and $p_1=0$), and the post-jump population is an independent copy of the same process started at $y-1+j$ and run for the remaining time $t-s$. In symbols,
--   $$(K_y(t))(\{k\})=e^{-\lambda y t}\mathbf{1}_{k=y}+\int_0^t \lambda y e^{-\lambda y s}\sum_{j\ge 0}p_j\,(K_{y-1+j}(t-s))(\{k\})\,ds.$$
--   The integrand is interval-integrable. No finite offspring mean is assumed.
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

theorem Kyprianou.Ch01.reverseLampertiPositiveTimeFirstJumpRenewal
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
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}) :
    (∀ t : ℝ≥0, ∀ k : ℕ, K 0 t k = (PMF.pure 0) k) ∧
      ∀ y : ℕ, 0 < y → ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ,
        IntervalIntegrable
          (fun s : ℝ =>
            ((rate : ℝ) * (y : ℝ)) * Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
              ∑' j : ℕ, (offspring j).toReal *
                (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
          volume 0 (t : ℝ) ∧
        (K y t k).toReal =
          (if k = y then Real.exp (-((rate : ℝ) * (y : ℝ) * (t : ℝ))) else 0) +
            ∫ s in (0 : ℝ)..(t : ℝ),
              ((rate : ℝ) * (y : ℝ)) * Real.exp (-(((rate : ℝ) * (y : ℝ)) * s)) *
                ∑' j : ℕ, (offspring j).toReal *
                  (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal := by
  sorry
