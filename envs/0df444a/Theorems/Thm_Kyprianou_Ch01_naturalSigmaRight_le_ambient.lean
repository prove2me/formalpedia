-- Prove2me | Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_le_ambient
-- name    : Kyprianou.Ch01.naturalSigmaRight_le_ambient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T16:48:25.828674+00:00
-- url     : https://prove2.me/theorems/7e3875f2-ed13-437a-9132-44b06ee35c9e
-- title:
--   Right-natural sigma-field embeds in the ambient measurable space
-- statement:
--   The right-continuous natural sigma-field of a process with ambient-measurable fixed-time sections is itself a sub-sigma-field of the ambient measurable space. Choose any deterministic time s>t and use the infimum definition of the right-natural filtration together with the already proved naturalSigma_le_ambient theorem. This is required to transfer natural-right stopping-time events to ambient measurability.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.13, right-continuous natural filtration.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_le_ambient
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.naturalSigmaRight_le_ambient
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (t : ℝ≥0) :
    naturalSigmaRight X t ≤ (inferInstance : MeasurableSpace Ω) := by sorry
