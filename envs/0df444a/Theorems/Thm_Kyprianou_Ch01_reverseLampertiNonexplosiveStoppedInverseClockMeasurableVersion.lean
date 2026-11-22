-- Prove2me | Theorems.Thm_Kyprianou_Ch01_reverseLampertiNonexplosiveStoppedInverseClockMeasurableVersion
-- name    : Kyprianou.Ch01.reverseLampertiNonexplosiveStoppedInverseClockMeasurableVersion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:40:03.196882+00:00
-- url     : https://prove2.me/theorems/efffa70f-388d-47f5-aaf1-bd6b06171153
-- title:
--   Sectionwise measurable stopped reciprocal-occupation inverse clock version under explicit non-explosion
-- statement:
--   Construct a measurable WithTop NNReal inverse-time version T(t,ω) agreeing simultaneously at every level t on a Q-conull event with the source min of inverseReciprocalOccupation X t and firstNegativePassage X. Start with the original Lebesgue-lintegral reciprocalOccupation definition. For fixed physical s its value is measurable in ω through the jointly measurable source version, Fubini/Tonelli for nonnegative products, and measurable set restrictions. It is monotone in s (an existing Proved lemma). The strict-upper-passage inverse can be represented as the infimum over a countable rational grid because any crossing I(s)>t persists for later times. Measurability of the rational infimum and of the first negative passage, by analogous rational hitting under all-path right continuity, makes T measurable for each t. Use a single measurable conull regularity event to ensure equality of the versions at all levels. Respect the source first-negative-passage stopping convention and the explicit hNoExplosion hypothesis. No invented continuity of an ENNReal integral or moment bound.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4 reverse Lamperti law, root theorem ac1b29c6-5525-4344-a03d-7469824736ed, connected witness parent 4c40c848-86b4-4c33-8f82-4106ca9fe438, mission 9919725d-217e-48cb-9cd1-bb779a69b820; pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Reuse Proved reciprocalOccupationMonotone d401e83a-e957-4235-98fe-1c200c964b6e, integerCompoundPoissonRightContinuousAE 89e2d356-663a-425c-afcd-ad3841267c58, and relevant first-passage/rational infimum proofs from Chapter 1.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.reverseLampertiNonexplosiveStoppedInverseClockMeasurableVersion
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation (integerCompoundPoisson y arrival marks) s ω) :
    ∀ y : ℕ, ∃ T : ℝ≥0 → Ω → WithTop ℝ≥0,
      (∀ t : ℝ≥0, Measurable (T t)) ∧
      ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
        T t ω =
          min (inverseReciprocalOccupation
            (integerCompoundPoisson y arrival marks) t ω)
            (firstNegativePassage
              (integerCompoundPoisson y arrival marks) ω) := by
  sorry
