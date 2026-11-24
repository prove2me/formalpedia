-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rightContinuous_of_sections
-- name    : Kyprianou.Ch01.rightContinuous_of_sections
-- status  : Disproved
-- author  : @pageman
-- created : 2026-11-24T19:45:59.371222+00:00
-- url     : https://prove2.me/theorems/4d35d1c7-31e2-4cd3-8fd8-6f4c369b4a0f
-- title:
--   Pathwise right-continuity from measurable sections alone (false)
-- statement:
--   Claim: measurable time sections alone force every path $t\mapsto X_t(\omega)$ to be right-continuous. This is the missing bridge from `firstNegativePassageMeasurable_of_sections` to `firstNegativePassageMeasurable_of_rightContinuous`. A single irrational spike path shows the claim is false.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rightContinuous_of_sections
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (_hX : ∀ t : ℝ≥0, Measurable (X t)) :
    ∀ ω : Ω, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => X s ω) (Set.Ici t) t := by
  sorry
