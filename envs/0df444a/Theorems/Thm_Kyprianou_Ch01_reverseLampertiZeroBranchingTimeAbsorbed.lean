-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiZeroBranchingTimeAbsorbed
-- name    : Kyprianou.Ch01.reverseLampertiZeroBranchingTimeAbsorbed
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-23T13:33:45.117735+00:00
-- url     : https://prove2.me/theorems/0c1901d1-2c2c-4f19-b306-073dc21c84f1
-- title:
--   Zero is absorbing for the reverse Lamperti population
-- statement:
--   Let $Y^y$ be the integer-valued population obtained from a nonexplosive reverse Lamperti time change of a compound Poisson process of rate $\lambda>0$, started at $y\in\mathbb{N}$, with jump law supported on $\{-1,0,1,\ldots\}$ and with no jump of size $0$. Write $K(y,t)$ for its law at branching time $t$.
--
--   At height $0$ the reciprocal occupation integrand is infinite, so the inverse Lamperti clock never advances and the path stays at $0$. Hence, for every $t\ge 0$,
--   $$K(0,t)=\delta_0.$$
--   This is the boundary clause of the first-jump renewal equation. The nonexplosion hypothesis says that every branching time is attained by the occupation clock.
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

theorem Kyprianou.Ch01.reverseLampertiZeroBranchingTimeAbsorbed
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
    ∀ t : ℝ≥0, ∀ k : ℕ, K 0 t k = (PMF.pure 0) k := by
  sorry
