-- Prove2me | Theorems.Thm_Kyprianou_Ch01_shiftedDriverRealisesPopulation
-- name    : Kyprianou.Ch01.shiftedDriverRealisesPopulation
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T19:00:37.053753+00:00
-- url     : https://prove2.me/theorems/0017dc59-c2e0-4ac4-8e4d-41e22c854a6d
-- title:
--   Shifted driver realises the population law
-- statement:
--   Let the interarrivals and marks of a compound Poisson driver have the infinite product law
--   $$\bigotimes_{n\in\mathbb{N}}\operatorname{Exp}(\lambda)\;\otimes\;\bigotimes_{n\in\mathbb{N}}\nu,$$
--   and let the shifted sequences, with the zeroth coordinate removed, again be a compound Poisson driver of rate $\lambda$ and jump law $\nu$. Let $K_z(s,m)$ be the probability that the original driver, started at height $z$, has population $m$ at the deterministic time $s$.
--
--   Then the shifted driver realises the same probabilities. For every height $z$, time $s$, and population size $m$,
--   $$\mathbb{Q}\big(Y^z_s=m\big)=K_z(s,m),$$
--   where $Y^z$ is the branching population built from the shifted interarrivals and marks. The no-explosion hypothesis is the one already assumed for the original driver: every occupation clock exceeds every finite time.
-- source:
--   Kyprianou (2006), Section 1.3.4; the shifted compound Poisson driver has the same population probabilities as the original driver.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.shiftedDriverRealisesPopulation
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω)
    (K : PopulationLaws)
    (hRealisation : ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      K y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k})
    (hTailDriver : IsCompoundPoissonDriver
      (fun n w => arrival (n + 1) w)
      (fun n w => marks (n + 1) w) rate jumpLaw Q)
    (hFullProductLaw : HasLaw
      (fun w (i : ℕ ⊕ ℕ) => (Sum.elim arrival marks i) w)
      (Measure.infinitePi
        (Sum.elim (fun _ : ℕ => expMeasure rate)
                  (fun _ : ℕ => jumpLaw))) Q)
    (z : ℕ) (s : ℝ≥0) (m : ℕ) :
    Q {ω | (compoundPoissonToBranching
        (integerCompoundPoisson z
          (fun n w => arrival (n + 1) w)
          (fun n w => marks (n + 1) w)) s ω).toNat = m} =
      K z s m := by
  sorry
