-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNegativePassageMeasurable_of_rightContinuous
-- name    : Kyprianou.Ch01.firstNegativePassageMeasurable_of_rightContinuous
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T19:19:54.578082+00:00
-- url     : https://prove2.me/theorems/00728185-0a12-4ffc-95d6-25c8c7250e7d
-- title:
--   Measurability of firstNegativePassage from sections and pathwise right-continuity
-- statement:
--   If each time section $X_t$ is measurable and every path $t\mapsto X_t(\omega)$ is right-continuous, then $\omega\mapsto\tau_0^-(X,\omega)$ is measurable. This is the right-continuous companion of `firstNegativePassageMeasurable_of_sections`.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNegativePassageMeasurable_of_rightContinuous
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : ∀ t : ℝ≥0, Measurable (X t))
    (hright : ∀ ω : Ω, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => X s ω) (Set.Ici t) t) :
    Measurable (fun ω : Ω => firstNegativePassage X ω) := by
  sorry
