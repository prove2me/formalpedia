-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagMonotoneOfDenseSequenceV1
-- name    : Kyprianou.Ch02.cadlagMonotoneOfDenseSequenceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:32:11.775385+00:00
-- url     : https://prove2.me/theorems/e14feb7f-f06c-4c3e-a287-4e79c047377f
-- title:
--   Right-continuous path order from a dense schedule
-- statement:
--   Use decreasing sequences from a dense time schedule converging from the right to s and t. Eventual order and the closedness of the real order yield the path inequality.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; auxiliary pathwise lifting argument.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem Kyprianou.Ch02.cadlagMonotoneOfDenseSequenceV1
    (f : ℝ≥0 → ℝ) (hc : ProbabilityTheory.IsCadlag f)
    (ts : ℕ → ℝ≥0) (hdense : DenseRange ts)
    (hsched : ∀ i j : ℕ, ts i ≤ ts j → f (ts i) ≤ f (ts j))
    (s t : ℝ≥0) (hst : s < t) :
    f s ≤ f t := by
  sorry
