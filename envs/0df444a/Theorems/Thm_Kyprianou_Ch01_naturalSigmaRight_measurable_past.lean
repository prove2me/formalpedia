-- Prove2me | Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_measurable_past
-- name    : Kyprianou.Ch01.naturalSigmaRight_measurable_past
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:00:43.496906+00:00
-- url     : https://prove2.me/theorems/0c345750-5228-4d5b-90b7-026d87f9a5d0
-- title:
--   Every past process coordinate is measurable in the right-natural sigma-field
-- statement:
--   For each u≤t the coordinate X(u) is measurable with respect to the right-continuous natural sigma-field at t. Apply the already proved raw natural-field adaptedness of X(u) and the inclusion of the raw natural field at t in its right-continuous refinement. This gives the basic adaptedness needed to treat the McKean discounted-value process as a right-natural supermartingale.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.13; adaptedness to the right-continuous natural filtration.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_le_naturalSigmaRight
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_measurable_past
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.naturalSigmaRight_measurable_past
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (u t : ℝ≥0) (hut : u ≤ t) :
    @Measurable Ω ℝ (naturalSigmaRight X t) inferInstance (X u) := by sorry
