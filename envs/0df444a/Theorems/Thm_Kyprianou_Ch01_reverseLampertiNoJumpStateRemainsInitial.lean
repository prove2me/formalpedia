-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNoJumpStateRemainsInitial
-- name    : Kyprianou.Ch01.reverseLampertiNoJumpStateRemainsInitial
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T13:33:44.336614+00:00
-- url     : https://prove2.me/theorems/9382d922-6a41-404a-99f0-f54469c1d381
-- title:
--   No jump before branching time keeps the initial population
-- statement:
--   Fix an initial population $y\ge 1$ and a branching time $t>0$. Branching time runs at speed $1/y$ while the path sits at $y$, so the first Lévy arrival $\tau_1$ falls after the Lévy time $yt$ if and only if the time-changed population has not jumped by branching time $t$.
--
--   On that event the state is still $y$. Therefore, for each $k\in\mathbb{N}$,
--   $$\mathbb{Q}\big(Y^y_t=k,\; \tau_1>yt\big)=\mathbf{1}_{k=y}\,\mathbb{Q}(\tau_1>yt).$$
--   The same compound-Poisson driver, jump support, and nonexplosion hypotheses as in the renewal equation are in force.
-- source:
--   A. E. Kyprianou, Fluctuations of Levy Processes with Applications, 2nd ed., Springer, Chapter 1, reverse Lamperti representation and the branching property.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNoJumpStateRemainsInitial
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
    Q {ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k ∧
        (y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω} =
      if k = y then
        Q {ω | (y : ℝ) * (t : ℝ) < ProbabilityTheory.arrival arrival 0 ω}
      else 0 := by
  sorry
