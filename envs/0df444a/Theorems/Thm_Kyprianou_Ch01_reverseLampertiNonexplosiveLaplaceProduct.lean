-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveLaplaceProduct
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveLaplaceProduct
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T10:00:33.334898+00:00
-- url     : https://prove2.me/theorems/2751c42b-5b1e-456f-a18d-6b09d02bd0f0
-- title:
--   Laplace product for the nonexplosive reverse Lamperti population
-- statement:
--   Let $K_y(t)$ be the law of the reverse Lamperti population obtained from an integer compound-Poisson process of rate $\lambda>0$, started at $y$, with offspring jump sizes $k-1$ and with a reciprocal occupation clock that does not explode. Write
--   $$\widehat K_y(t,\phi)=\sum_{n\ge 0} K_y(t)(\{n\}) e^{-\phi n}$$
--   for the Laplace transform at frequency $\phi>0$. The claim is the product formula
--   $$\widehat K_{a+b}(t,\phi)=\widehat K_a(t,\phi)\,\widehat K_b(t,\phi).$$
--   This is the transform form of independent-ancestor convolution. No finite offspring mean is assumed. The identity is the remaining probabilistic input once uniqueness of probability mass functions with a common Laplace transform is granted.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, reverse Lamperti law, equation (1.19), Laplace form of the branching convolution

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveLaplaceProduct
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
    (a b : ℕ) (t : ℝ≥0) (phi : ℝ) (hphi : 0 < phi) :
    branchingLaplace K (a + b) t phi =
      branchingLaplace K a t phi * branchingLaplace K b t phi := by
  sorry
