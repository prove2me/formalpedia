-- Prove2me | Theorems.Thm_Kyprianou_Ch01_nonnegativeSInfTranslatedImage
-- name    : Kyprianou.Ch01.nonnegativeSInfTranslatedImage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:53:06.268876+00:00
-- url     : https://prove2.me/theorems/405024e8-9011-410a-8426-4698907c6225
-- title:
--   Infimum of a translated nonempty subset of the nonnegative reals
-- statement:
--   A strictly nonempty set of nonnegative times has translated infimum equal to its original infimum plus the nonnegative translation. Both sets are bounded below by zero; establish the result using le_csInf, csInf_le and the standard subtraction identity. This is the missing order-theoretic component of the shifted first-negative-passage clock in Chapter 1.
-- source:
--   Deterministic order-theoretic translation lemma for Kyprianou (2006), Section 1.3.4, first-mark time shift.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.nonnegativeSInfTranslatedImage
    (a : ℝ≥0) (S : Set ℝ≥0) (hS : S.Nonempty) :
    sInf ((fun s : ℝ≥0 => a + s) '' S) = a + sInf S := by
  sorry
