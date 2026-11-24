-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagTruncatedJumpLeTimeAtomV1
-- name    : Kyprianou.Ch02.cadlagTruncatedJumpLeTimeAtomV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:15:14.595484+00:00
-- url     : https://prove2.me/theorems/5644a52c-fef4-4513-b081-a806752bda10
-- title:
--   A càdlàg jump is bounded by the atom of an increment-dominating measure
-- statement:
--   Take an increasing sequence of times strictly below the given positive time. Apply the increment bound and continuity from above of the finite measure to obtain a bound by its atom; the linear error vanishes.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch02.cadlagTruncatedJumpLeTimeAtomV1
    (f : ℝ≥0 → ℝ) (hf : IsCadlag f) (m : Measure ℝ≥0)
    (T : ℝ≥0) (C : ℝ) (hm : m (Set.Ioc 0 T) < ⊤)
    (hinc : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      ENNReal.ofReal (min (1 : ℝ) |f t - f s|) ≤
        m (Set.Ioc s t) + ENNReal.ofReal (C * ((t : ℝ) - (s : ℝ)))) :
    ∀ u : Set.Ioc (0 : ℝ≥0) T,
      ENNReal.ofReal (min (1 : ℝ) |f u - Function.leftLim f u|) ≤ m {u.val} := by
  sorry
