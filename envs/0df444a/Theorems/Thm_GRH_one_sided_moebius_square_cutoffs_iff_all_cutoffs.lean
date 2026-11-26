-- Prove2me | Theorems.Thm_GRH_one_sided_moebius_square_cutoffs_iff_all_cutoffs
-- name    : GRH.one_sided_moebius_square_cutoffs_iff_all_cutoffs
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T20:55:35.5548+00:00
-- url     : https://prove2.me/theorems/5acd743d-2eec-4c78-94aa-008ce7829ac4
-- title:
--   Upper Möbius power bounds at squares interpolate to every integer cutoff
-- statement:
--   For any residue class, even a nonunit class, and every exponent σ at least one half, a one-sided upper power bound at all perfect squares is equivalent to the same order of upper bound at every natural cutoff.
-- source:
--   Arithmetic reduction of the exact centered progression estimate. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_GRH_OneSidedMoebius

open MeasureTheory Set GRH.OneSidedMoebius

theorem GRH.one_sided_moebius_square_cutoffs_iff_all_cutoffs {q : ℕ} (a : ZMod q) (σ : ℝ) (hσ : (1/2 : ℝ) ≤ σ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ, residue a (u^2) ≤ C*((u:ℝ)^2+1)^σ) ↔
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, residue a N ≤ D*((N:ℝ)+1)^σ := by sorry
