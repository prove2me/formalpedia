-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_rationalApproxEvent
-- name    : Kyprianou.Ch01.firstUpperPassage_rationalApproxEvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T19:00:54.665765+00:00
-- url     : https://prove2.me/theorems/bb15d325-9b00-4017-8e06-900d8dca6043
-- title:
--   Continuous strict level passage as a countable intersection of rational crossings
-- statement:
--   For an everywhere-continuous real process, the event of strict upper passage by t is exactly the countable intersection of rational crossing events observed by the deterministic horizons t+(v-t)/(n+2), for every v>t. The proof combines the published rational-approach characterisation with an Archimedean cofinality lemma. This full event equivalence is a technical child for proving right-continuous natural stopping-time measurability.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and Exercise 1.6(i), rational approximation of strict upper-passage events, prerequisite for Chapter 1 milestone 5623d362-55e7-4f38-be0c-f4933c607e17.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01 Set Filter
open scoped NNReal
set_option autoImplicit false
universe u

theorem Kyprianou.Ch01.firstUpperPassage_rationalApproxEvent
    {Ω : Type u} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) (t v : ℝ≥0) (htv : t < v) :
    {ω | Kyprianou.Ch01.firstUpperPassage X s ω ≤ (t : WithTop ℝ≥0)} =
      ⋂ n : ℕ, {ω | ∃ q : ℚ, 0 < (q : ℝ) ∧
        (q : ℝ) ≤ ((t + (v - t) / ((n : ℝ≥0) + 2) : ℝ≥0) : ℝ) ∧
        s < X (Real.toNNReal (q : ℝ)) ω} := by
  sorry
