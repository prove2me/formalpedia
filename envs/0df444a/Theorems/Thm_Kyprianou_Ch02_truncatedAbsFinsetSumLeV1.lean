-- Prove2me | Theorems.Thm_Kyprianou_Ch02_truncatedAbsFinsetSumLeV1
-- name    : Kyprianou.Ch02.truncatedAbsFinsetSumLeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:15:12.814553+00:00
-- url     : https://prove2.me/theorems/88ceb168-37ed-4fd5-9453-856032d25e3e
-- title:
--   Truncated absolute weight of a finite sum is bounded by the sum of truncated weights
-- statement:
--   The truncated absolute value is subadditive: if either summand exceeds one the result is immediate, and otherwise use the absolute-value triangle inequality. Induct over the finite set.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib
open scoped ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch02.truncatedAbsFinsetSumLeV1
    {ι : Type} (S : Finset ι) (g : ι → ℝ) :
    ENNReal.ofReal (min (1 : ℝ) |∑ i ∈ S, g i|) ≤
      ∑ i ∈ S, ENNReal.ofReal (min (1 : ℝ) |g i|) := by
  sorry
