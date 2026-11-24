-- Prove2me | Theorems.Thm_Kyprianou_Ch02_cadlagSmallJumpMassLeTimeMeasureV1
-- name    : Kyprianou.Ch02.cadlagSmallJumpMassLeTimeMeasureV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T23:15:17.366974+00:00
-- url     : https://prove2.me/theorems/2f3f024e-7867-45eb-9492-d4b09d593021
-- title:
--   Actual small-jump mass is bounded by an increment-dominating time measure
-- statement:
--   Bound each small jump by its time atom using the left-limit argument. Sum over finite sets of distinct times using additivity, then take the supremum of finite sums.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch02.cadlagSmallJumpMassLeTimeMeasureV1
    (f : ℝ≥0 → ℝ) (hf : IsCadlag f) (m : Measure ℝ≥0)
    (T : ℝ≥0) (C : ℝ) (hm : m (Set.Ioc 0 T) < ⊤)
    (hinc : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      ENNReal.ofReal (min (1 : ℝ) |f t - f s|) ≤
        m (Set.Ioc s t) + ENNReal.ofReal (C * ((t : ℝ) - (s : ℝ)))) :
    (∑' u : Set.Ioc (0 : ℝ≥0) T,
      ENNReal.ofReal (if |f u - Function.leftLim f u| ≤ (1 : ℝ)
        then |f u - Function.leftLim f u| else 0)) ≤ m (Set.Ioc 0 T) := by
  sorry
