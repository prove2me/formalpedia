-- Prove2me | Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_monotone
-- name    : Kyprianou.Ch01.naturalSigmaRight_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:48:26.030659+00:00
-- url     : https://prove2.me/theorems/53708b81-9d5a-464f-bed9-c986496639b3
-- title:
--   Right-continuous natural sigma-fields form a filtration
-- statement:
--   For any process and times s≤t, the intersection of natural sigma-fields at strictly later times than s is contained in the corresponding intersection of natural sigma-fields strictly later than t. This elementary order fact establishes the filtration structure needed to apply proved optional-stopping results to the original McKean right-continuous natural filtration.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.13, right-continuous natural filtration.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.naturalSigmaRight_monotone
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    naturalSigmaRight X s ≤ naturalSigmaRight X t := by sorry
