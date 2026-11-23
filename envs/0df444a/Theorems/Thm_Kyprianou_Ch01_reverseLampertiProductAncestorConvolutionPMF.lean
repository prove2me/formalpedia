-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiProductAncestorConvolutionPMF
-- name    : Kyprianou.Ch01.reverseLampertiProductAncestorConvolutionPMF
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:56:15.27915+00:00
-- url     : https://prove2.me/theorems/5b1ca273-cfe5-4181-a0f7-1b7b5ac43fa8
-- title:
--   Product-law independent ancestor sum equals convolution of the realised population PMFs
-- statement:
--   For the same source realisation K(y,t,k)=Q(Y^y_t=k), the distribution of Y^a_t(ω1)+Y^b_t(ω2) under independent product Q×Q is the PMF convolution (K a t).bind (fun n => (K b t).map (fun m => n+m)). Prove using the already Proved AEMeasurable reverse Lamperti state, measurability of singleton events, product measure and countable sum. This is a measure-theoretic identity independent of the substantive branching coupling.
-- source:
--   Generic product-measure convolution identity, applied to Proved Kyprianou.Ch01.reverseLampertiNonexplosiveStateAEMeasurable and the original population realisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiProductAncestorConvolutionPMF
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
    (a b : ℕ) (t : ℝ≥0) (k : ℕ) :
    (Q.prod Q)
      {ζ : Ω × Ω |
        (compoundPoissonToBranching
          (integerCompoundPoisson a arrival marks) t ζ.1).toNat +
        (compoundPoissonToBranching
          (integerCompoundPoisson b arrival marks) t ζ.2).toNat = k} =
    ((K a t).bind (fun n => (K b t).map (fun m => n + m))) k := by
  sorry
