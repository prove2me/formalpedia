-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingRateGeneratorConservativeSemigroupUnique
-- name    : Kyprianou.Ch01.branchingRateGeneratorConservativeSemigroupUnique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:31:51.340513+00:00
-- url     : https://prove2.me/theorems/abf1b453-26bc-421b-b350-3ce810bb8479
-- title:
--   Uniqueness of conservative continuous-time Markov branching semigroup with a prescribed offspring generator
-- statement:
--   Establish uniqueness among conservative PMF-valued Markov branching semigroups with branching convolution, deterministic initial laws and identical finite-state offspring Q-matrix q(y,k) (diagonal -rate*y when offspring mass at 1 is zero, off-diagonal rate*y*p_(k+1-y)). No finite offspring first moment is assumed; conservative PopulationLaws are total probability measures on ℕ. One rigorous route is to use the branching property to express the population generating function from y ancestors as the yth power of its one-ancestor generating function, derive the Kolmogorov generating-function evolution, then use uniqueness for the scalar ODE on the open unit interval (offspring PGF locally Lipschitz strictly inside 1 even when the first moment diverges). Prove equality of PMFs from equality of generating functions at all z in (0,1), or alternatively use the minimal conservative Q-semigroup uniqueness theorem. Explicitly rule out any unproved uniqueness claim for explosive/sub-stochastic paths. The generator here scales with population y, unlike the already Proved constant-rate `lampertiLatticeGeneratorSemigroupUnique`; never apply that theorem to this rate matrix. This theorem is a direct dependency of the root reverse Lamperti proof.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, continuous-time Markov branching semigroup. Main root ac1b29c6-5525-4344-a03d-7469824736ed. Def_Kyprianou_Ch01_BranchingGenerator `IsBranchingRateGenerator`, Def_Kyprianou_Ch01_BranchingClocks `PopulationLaws`, `HasBranchingProperty`, `IsPopulationMarkovSemigroup`. Branching generating-function derivation; do not confuse with proved lattice constant-rate uniqueness 91f06661-95bf-430e-8cec-cb3e0fcdab98.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingRateGeneratorConservativeSemigroupUnique
    (rate : ℝ≥0) (offspring : PMF ℕ)
    (hNoZeroJumps : offspring 1 = 0)
    (K₁ K₂ : PopulationLaws)
    (hBranch₁ : HasBranchingProperty K₁)
    (hBranch₂ : HasBranchingProperty K₂)
    (hSemi₁ : IsPopulationMarkovSemigroup K₁)
    (hSemi₂ : IsPopulationMarkovSemigroup K₂)
    (hInit₁ : ∀ y : ℕ, K₁ y 0 = PMF.pure y)
    (hInit₂ : ∀ y : ℕ, K₂ y 0 = PMF.pure y)
    (hGen₁ : IsBranchingRateGenerator K₁ rate offspring)
    (hGen₂ : IsBranchingRateGenerator K₂ rate offspring) :
    K₁ = K₂ := by
  sorry
