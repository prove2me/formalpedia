-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveJointClockVersion
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveJointClockVersion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:00:24.238091+00:00
-- url     : https://prove2.me/theorems/4c40c848-86b4-4c33-8f82-4106ca9fe438
-- title:
--   A jointly measurable compound-Poisson population and measurable inverse-clock version agreeing with the reverse Lamperti path
-- statement:
--   Under the exact integer-supported compound Poisson driver and global reciprocal-occupation non-explosion assumptions, construct for each initial population y (1) a jointly measurable integer-valued time/sample process W, and (2) globally measurable WithTop NNReal inverse-time-change coordinates T(t,ω), such that the original reverse Lamperti state `compoundPoissonToBranching (integerCompoundPoisson y arrival marks) t ω` converted with Int.toNat equals the absorbing-zero evaluation at T of W, simultaneously for every time t on one common Q-conull event. W can be a jointly measurable right-continuous version of the source integer compound Poisson path; T must represent the minimum of its inverse reciprocal occupation clock and first negative passage. This is the genuine outstanding clock/first-passage/joint process measurability theorem needed for original reverse Lamperti Q event probability statement, not a redefinition of the source process. No finite first offspring moment assumption.
-- source:
--   Kyprianou (2006) Ch1 §1.3.4, Def_Kyprianou_Ch01_LampertiInverse. Connected rootward parent reverseLampertiNonexplosiveStateAEMeasurable UUID 5b4cef8f-ef05-4bcd-9c85-4c110d728c6e and original root ac1b29c6-5525-4344-a03d-7469824736ed. Reuse proved integerCompoundPoissonRightContinuousAE 89e2d356-663a-425c-afcd-ad3841267c58, rightContinuous_measurable_sections_joint_evaluation 8aafec11-d8a5-443c-9386-270a0d5c8a04, generic measurableWithTopIntegerRandomTimeEvaluation (published this session).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveJointClockVersion
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
    ∀ y : ℕ,
      ∃ (W : ℝ≥0 → Ω → ℤ)
        (T : ℝ≥0 → Ω → WithTop ℝ≥0),
        Measurable (fun z : ℝ≥0 × Ω => W z.1 z.2) ∧
        (∀ t : ℝ≥0, Measurable (T t)) ∧
        (∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
          (compoundPoissonToBranching
            (integerCompoundPoisson y arrival marks) t ω).toNat =
          (if T t ω = ⊤ then (0 : ℤ)
           else W ((T t ω).untopD 0) ω).toNat) := by
  sorry
