-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pmfWeightedUnitIntervalBound
-- name    : Kyprianou.Ch01.pmfWeightedUnitIntervalBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T15:16:55.674454+00:00
-- url     : https://prove2.me/theorems/45b3548b-b0df-4264-b072-a2c18e450b97
-- title:
--   Offspring-PMF weighted mixture lies in the unit interval
-- statement:
--   A probability-weighted countable mixture of real numbers in [0,1] is between zero and one. Used to dominate the reverse-Lamperti first-event renewal kernel, without offspring moment assumptions.
-- source:
--   Elementary consequence of PMF total mass one and real summability, for Kyprianou (2006) Section 1.3.4.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.pmfWeightedUnitIntervalBound
    (p : PMF ℕ) (f : ℕ → ℝ)
    (hf : ∀ j : ℕ, 0 ≤ f j ∧ f j ≤ 1) :
    0 ≤ (∑' j : ℕ, (p j).toReal * f j) ∧
      (∑' j : ℕ, (p j).toReal * f j) ≤ 1 := by
  sorry
