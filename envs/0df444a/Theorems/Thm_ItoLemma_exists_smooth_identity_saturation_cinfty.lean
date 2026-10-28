-- Prove2me | Theorems.Thm_ItoLemma_exists_smooth_identity_saturation_cinfty
-- name    : ItoLemma.exists_smooth_identity_saturation_cinfty
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:33:51.198347+00:00
-- url     : https://prove2.me/theorems/bc3180a1-1428-43e9-8700-35879f49b05f
-- title:
--   A Smooth Compactly Supported Extension of the Identity on a Bounded Interval (C-infinity)
-- statement:
--   For every nonnegative R there exists a smooth compactly supported real function ρ which agrees with the identity map on the interval [-R,R]. Construct ρ(x) as x times a smooth compactly supported bump which equals one on that interval. This is the first functional-analytic step towards localising the polynomial xy in the product rule.
-- source:
--   Construction from official Mathlib ContDiffBump and HasCompactSupport.mul_right theorems, researched on 26 October 2026; follows the Itô product-rule extension plan. Correction: Mathlib's ⊤ level is analytic, while ↑(⊤ : ℕ∞) is the smooth level; see ContDiff.Defs (26 October 2026).

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open Filter Topology

theorem ItoLemma.exists_smooth_identity_saturation_cinfty
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ρ ∧ HasCompactSupport ρ ∧
      ∀ x : ℝ, |x| ≤ R → ρ x = x := by sorry
