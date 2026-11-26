-- Prove2me | Theorems.Thm_GRH_zeta_zero_free_of_one_sided_mertens_bound
-- name    : GRH.zeta_zero_free_of_one_sided_mertens_bound
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T20:55:34.297522+00:00
-- url     : https://prove2.me/theorems/fbee581d-caab-49e2-8355-073eca77e8e2
-- title:
--   A one-sided Mertens bound excludes zeta zeros to its right
-- statement:
--   For 0 < θ < 1, an upper bound M(n) ≤ C(n+1)^θ for every natural n implies ζ(s) is nonzero whenever Re s > θ and s differs from one.
-- source:
--   Arithmetic reduction of the exact centered progression estimate. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 The positive Mellin-transform argument is adapted, with attribution and license in the Lean source, from pitimespi. https://prove2.me/submissions/371c6c95-d927-4bbe-822c-d3f6df8f83e7

import Definitions.Def_GRH_OneSidedMoebius

open MeasureTheory Set GRH.OneSidedMoebius

theorem GRH.zeta_zero_free_of_one_sided_mertens_bound (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, mertens n ≤ C*((n:ℝ)+1)^θ) :
    ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by sorry
