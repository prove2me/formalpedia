-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_rawNaturalPast_later
-- name    : Kyprianou.Ch01.firstUpperPassage_le_rawNaturalPast_later
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:53:32.905495+00:00
-- url     : https://prove2.me/theorems/111fb72c-ef44-4806-964d-5eab8cd1537b
-- title:
--   Strict level-crossing event is measurable in every strictly later natural sigma-field
-- statement:
--   For a real continuous path process, the event that its strict upward level-passage time is at most t is measurable using observations up to any deterministic v>t. This technical lemma is the quantitative filtration step needed to prove strict passage is a stopping time for the right-continuous natural filtration. Intended proof: represent passage by a decreasing sequence of rational crossing events before t+epsilon_n, where epsilon_n decreases to zero and t+epsilon_n<v, then use countable intersections and published rational-crossing measurability. No optional stopping or strong Markov hypothesis is assumed.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and Exercise 1.6(i), pp. 8–9 and 28–29; technical reduction of published Chapter 1 milestone 5623d362-55e7-4f38-be0c-f4933c607e17.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.firstUpperPassage_le_rawNaturalPast_later
    {Ω : Type u} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) (t v : ℝ≥0) (htv : t < v) :
    @MeasurableSet Ω (Kyprianou.Ch01.naturalSigma X v)
      {ω | Kyprianou.Ch01.firstUpperPassage X s ω ≤
        (t : WithTop ℝ≥0)} := by
  sorry
