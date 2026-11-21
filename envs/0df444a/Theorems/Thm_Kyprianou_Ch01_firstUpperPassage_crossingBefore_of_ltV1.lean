-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_crossingBefore_of_ltV1
-- name    : Kyprianou.Ch01.firstUpperPassage_crossingBefore_of_ltV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T23:32:49.943186+00:00
-- url     : https://prove2.me/theorems/464150a6-1f0a-4a8b-b060-59a8dd17ef9a
-- title:
--   A finite strict first-passage before a horizon gives a strict crossing before that horizon
-- statement:
--   The strict first-passage time is the infimum of the nonempty strict-crossing set S, or infinity if no crossing exists. If it is strictly before a finite time t, the latter case is impossible and the infimum satisfies sInf S<t. The pinned Mathlib theorem exists_lt_of_csInf_lt supplies v∈S below t. This is a deterministic time-bound lemma with no probabilistic assumptions and is needed to formalise right continuity of first passage under finite crossing.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, strict crossing infimum.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01 Set
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassage_crossingBefore_of_ltV1
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s : ℝ) (ω : Ω) (t : ℝ≥0)
    (h : firstUpperPassage X s ω < (t : WithTop ℝ≥0)) :
    ∃ v : ℝ≥0, 0 < v ∧ v < t ∧ s < X v ω := by
  sorry
