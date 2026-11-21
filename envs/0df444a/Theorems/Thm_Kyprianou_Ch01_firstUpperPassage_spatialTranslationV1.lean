-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_spatialTranslationV1
-- name    : Kyprianou.Ch01.firstUpperPassage_spatialTranslationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:30:46.102198+00:00
-- url     : https://prove2.me/theorems/63576eb5-85ef-447d-a5cc-fff509b8cbb2
-- title:
--   First strictly upper passage is invariant under common spatial translation
-- statement:
--   Strict upper first-passage times are invariant under simultaneously translating every path height and the upper barrier by the same real constant. The existence of a strict crossing and the crossing-time set are unchanged because s+c < X_t+c iff s<X_t. The result follows by unfolding the exact pinned firstUpperPassage definition and simplifying both the existence test and infimum set. This is the deterministic spatial homogeneity input needed for the strong Markov proof of stationary inverse-Gaussian increments.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5, spatial translation invariance of upper passage.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstUpperPassage_spatialTranslationV1
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (s c : ℝ) (ω : Ω) :
    firstUpperPassage (fun t ω => X t ω + c) (s + c) ω =
      firstUpperPassage X s ω := by sorry
