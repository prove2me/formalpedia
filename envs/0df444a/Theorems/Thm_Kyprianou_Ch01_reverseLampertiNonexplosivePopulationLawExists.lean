-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosivePopulationLawExists
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosivePopulationLawExists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:40:11.516796+00:00
-- url     : https://prove2.me/theorems/eedf99b6-d4d0-428c-bd29-d18cc4800986
-- title:
--   Construct a conservative PMF transition family from nonexplosive reverse Lamperti paths
-- statement:
--   Given the exact integer-supported compound-Poisson driver and global reciprocal-clock non-explosion assumption, construct a genuine PopulationLaws K: for each y,t, K y t is a PMF on ℕ whose kth mass equals Q of the exact toNat inverse Lamperti event. Prove each fixed-time time-changed state is Q-a.e. measurable, form the probability law by pushing forward Q and converting via Measure.toPMF, prove point-mass identity and initial state K y 0=δ_y. Every PMF must have full mass one. This is the conservative-law and measurability component of the reverse Lamperti existence parent, separate from Markov/branching and generator calculations.
-- source:
--   Kyprianou (2006) §1.3.4 reverse Lamperti, source definitions and Proved compoundPoissonReverseRecoveryPathwise UUID 41fefac4-5573-460f-ba9d-981ea052b900. Connected parent reverseLampertiNonexplosiveConstructsBranchingLaw add9a198-d73d-4166-b02f-7086a5eb80b0, root ac1b29c6-5525-4344-a03d-7469824736ed.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosivePopulationLawExists
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
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω) :
    ∃ K : PopulationLaws,
      (∀ y : ℕ, K y 0 = PMF.pure y) ∧
      ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
        K y t k =
          Q {ω | (compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks) t ω).toNat = k} := by
  sorry
