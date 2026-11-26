-- Prove2me | Theorems.Thm_GRH_one_sided_moebius_progression_upper_at_squares
-- name    : GRH.one_sided_moebius_progression_upper_at_squares
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T20:55:32.584402+00:00
-- url     : https://prove2.me/theorems/1568df8a-9b72-5457-ab22-fa30c07ae286
-- title:
--   One-sided Möbius power cancellation in unit residue classes at perfect squares
-- statement:
--   For every positive modulus q, unit residue class a, and 1/2 < σ < 1, prove that the raw sum of the Möbius coefficients μ(k) for k ≤ u² in class a is at most C(u²+1)^σ for every natural u. The nonnegative constant may depend on q, a and σ.
-- source:
--   Arithmetic reduction of the exact centered progression estimate. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_GRH_OneSidedMoebius

open GRH.OneSidedMoebius

theorem GRH.one_sided_moebius_progression_upper_at_squares
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1/2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ, residue a (u^2) ≤ C*((u:ℝ)^2+1)^σ := by sorry
