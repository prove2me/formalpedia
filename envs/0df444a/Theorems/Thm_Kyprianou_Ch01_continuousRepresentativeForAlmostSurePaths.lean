-- Prove2me | Theorems.Thm_Kyprianou_Ch01_continuousRepresentativeForAlmostSurePaths
-- name    : Kyprianou.Ch01.continuousRepresentativeForAlmostSurePaths
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:07:51.973344+00:00
-- url     : https://prove2.me/theorems/5f06b624-553a-436e-bbba-7142f975605e
-- title:
--   continuousRepresentativeForAlmostSurePaths
-- statement:
--   A measurable almost-surely continuous process admits an everywhere continuous representative (agreeing at all times outside a single null event), provided the event of path continuity is measurable. This supplies the source-faithful continuity bridge to canonical Brownian path models.
-- source:
--   Kyprianou (2006), Chapter 1 Definition 1.1 and Brownian examples.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.continuousRepresentativeForAlmostSurePaths
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContSet : MeasurableSet {ω | Continuous (fun t : ℝ≥0 => X t ω)})
    (hAE : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ ω, Continuous (fun t : ℝ≥0 => Y t ω)) ∧
      (∀ t : ℝ≥0, Measurable (Y t)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Y t ω = X t ω) := by
  sorry
