-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveStateAEAndInitialMass
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveStateAEAndInitialMass
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T20:47:42.451634+00:00
-- url     : https://prove2.me/theorems/274da951-c8a4-49c3-a325-3820978f88fd
-- title:
--   A.e. measurability and exact initial-state atom masses of the nonexplosive reverse Lamperti population
-- statement:
--   For each starting integer y and inverse Lamperti time t, prove the exact natural-valued state obtained from the lattice compound Poisson path and its reciprocal occupation inverse is Q-a.e. measurable. Prove separately that at t=0 its probability distribution has point mass (PMF.pure y) k for every state k, using the driver starting state and first-passage/clock conventions. Handle the possibility of zero and negative original lattice paths, and use the supplied explicit global reciprocal-clock non-explosion event for all-time clock inversion. These are the actual measurability and initial-condition obligations needed to define the reverse transition PMF via the proven generic probability-to-PMF lemma; no finite offspring mean is assumed.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4; Def_Kyprianou_Ch01_LampertiInverse, Def_Kyprianou_Ch01_BranchingGenerator. Connected parent reverseLampertiNonexplosivePopulationLawExists eedf99b6-d4d0-428c-bd29-d18cc4800986 and root ac1b29c6-5525-4344-a03d-7469824736ed. Potential reuse integerCompoundPoissonFixedTimeMeasurable 4a215c58-846c-47b2-990a-fad256013ece and compoundPoissonReverseRecoveryPathwise 41fefac4-5573-460f-ba9d-981ea052b900.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveStateAEAndInitialMass
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
    (∀ (y : ℕ) (t : ℝ≥0),
      AEMeasurable
        (fun ω : Ω => (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat) Q) ∧
    (∀ (y k : ℕ),
      Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) 0 ω).toNat = k} =
        (PMF.pure y) k) := by
  sorry
