-- Prove2me | Theorems.Thm_ItoLemma_exists_smooth_cutoff_with_plateau_cinfty
-- name    : ItoLemma.exists_smooth_cutoff_with_plateau_cinfty
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:33:47.785842+00:00
-- url     : https://prove2.me/theorems/8cfe1557-67e3-4ac7-be22-7d31924543cf
-- title:
--   Smooth Compactly Supported Cutoff with a Prescribed Plateau (C-infinity)
-- statement:
--   For every nonnegative radius R there exists an infinitely differentiable, compactly supported real function φ that equals one whenever |x|≤R and equals zero whenever |x|≥R+2. Such cutoffs let bounded smooth functions agree with an unbounded polynomial on a prescribed bounded region, enabling a rigorous product rule through the existing bounded-derivative vector Itô formula.
-- source:
--   Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension and ContDiffBump, as documented in official Mathlib sources on 26 October 2026, together with the accepted vector Itô formula in Prove2Me. Correction: Mathlib's ⊤ level is analytic, while ↑(⊤ : ℕ∞) is the smooth level; see ContDiff.Defs (26 October 2026).

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Filter Topology

theorem ItoLemma.exists_smooth_cutoff_with_plateau_cinfty
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ φ : ℝ → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) φ ∧ HasCompactSupport φ ∧
      (∀ x : ℝ, |x| ≤ R → φ x = 1) ∧
      (∀ x : ℝ, R + 2 ≤ |x| → φ x = 0) := by sorry
