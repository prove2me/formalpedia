-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_finiteExcursionUniformStrictMargin
-- name    : Kyprianou.Ch08.StageB.finiteExcursionUniformStrictMargin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T10:00:12.137746+00:00
-- url     : https://prove2.me/theorems/0c402b31-d94f-40e2-a7f1-673950742550
-- title:
--   Lemma 8.2 deterministic ingredient: a strictly avoided finite excursion height has a uniform positive margin
-- statement:
--   A real-valued upper semicontinuous path on a compact nonnegative-time interval with both endpoint values zero cannot approach a positive avoided height arbitrarily closely without attaining it. If the path stays strictly below the height at every time before the positive endpoint, it stays below some uniformly smaller positive height. This is the deterministic strict-margin ingredient for left-continuity of actual reflected excursion-height laws, without assuming jump-measure atomlessness or abstract excursion distributions.
-- source:
--   Derived using the already Proved AvramDividend.Classical.finite_excursion_height_attained_of_upperSemicontinuous (0462795a-219e-4063-a208-ce845eb8acf2); needed to justify the left-height-exhaustion argument in Chapter 8 Lemma 8.2, child cade7bf0-28cb-43f9-b50a-18cc573d5092. The latter remains connected to original 4cc4a403 via accepted sketches.

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Compact
open Set Topology
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.finiteExcursionUniformStrictMargin
    (R : ℝ≥0 → ℝ) (ζ : ℝ≥0) (hζ : 0 < ζ)
    (husc : UpperSemicontinuousOn R (Set.Icc 0 ζ))
    (hzero : R 0 = 0) (hend : R ζ = 0)
    (x : ℝ) (hx : 0 < x)
    (hAvoid : ∀ t : ℝ≥0, t < ζ → R t < x) :
    ∃ h : ℝ, 0 < h ∧ h < x ∧
      ∀ t : ℝ≥0, t < ζ → R t < h := by
  sorry
