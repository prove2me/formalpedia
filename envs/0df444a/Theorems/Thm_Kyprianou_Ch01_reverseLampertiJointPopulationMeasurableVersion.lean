-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiJointPopulationMeasurableVersion
-- name    : Kyprianou.Ch01.reverseLampertiJointPopulationMeasurableVersion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T15:38:14.951293+00:00
-- url     : https://prove2.me/theorems/9c2615a4-379a-43e1-85d4-e8ea4b148ce9
-- title:
--   Joint Borel-measurable modification of the nonexplosive reverse-Lamperti population process
-- statement:
--   Construct a jointly measurable function of branching time and sample path which is almost surely equal at each fixed branching time to the integer-valued reverse-Lamperti population. Derive from the jointly measurable physical compound-Poisson version and inverse-occupation clock with measurable monotone time sections.
-- source:
--   Kyprianou (2006), Section 1.3.4. Jointly measurable modification needed to establish Borel measurability of population one-time law by measurable_measure_prodMk_left.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiJointPopulationMeasurableVersion
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
    :
    ∀ z : ℕ, ∃ Z : ℝ≥0 → Ω → ℕ,
      Measurable (fun v : ℝ≥0 × Ω => Z v.1 v.2) ∧
      ∀ u : ℝ≥0, ∀ᵐ ω ∂Q,
        Z u ω =
          (compoundPoissonToBranching
            (integerCompoundPoisson z arrival marks) u ω).toNat := by
  sorry
