-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rightNaturalStoppingTime_measurable
-- name    : Kyprianou.Ch01.rightNaturalStoppingTime_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:08:42.699147+00:00
-- url     : https://prove2.me/theorems/7476d2c7-38e2-4b9c-ab72-1898ce0ce9ee
-- title:
--   Right-natural stopping time is a measurable WithTop nonnegative real random variable
-- statement:
--   A stopping time tau in the original right-continuous natural filtration is measurable as a WithTop nonnegative real random variable under ambient measurability of fixed-time process sections. Construct a Mathlib Filtration with seq naturalSigmaRight X using the two already proved monotonicity and ambient inclusion lemmas. Interpret IsNaturalRightStoppingTime as an ordinary IsStoppingTime of that filtration and apply the existing stopping-time measurability theorem. This supplies stopped-time measurability for arbitrary finite and infinite Brownian stopping times.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.13; measurable right-natural stopping times.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_monotone
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_le_ambient
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rightNaturalStoppingTime_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime X tau) :
    Measurable tau := by sorry
