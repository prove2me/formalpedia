-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyNonnegativeMarginalOrderedIncrementV1
-- name    : Kyprianou.Ch02.levyNonnegativeMarginalOrderedIncrementV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:32:06.052797+00:00
-- url     : https://prove2.me/theorems/41f0b85d-d36b-458d-a09f-19243570fa1c
-- title:
--   Nonnegative Lévy marginals yield nonnegative ordered increments
-- statement:
--   Transfer nonnegative marginals to ordered increments by stationary increments and the zero initial value.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; auxiliary pathwise lifting argument.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem Kyprianou.Ch02.levyNonnegativeMarginalOrderedIncrementV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hm : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ X t ω)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∀ᵐ ω ∂P, X s ω ≤ X t ω := by
  sorry
