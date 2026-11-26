-- Prove2me | Theorems.Thm_GRH_centered_moebius_bound_iff_lower_bound_at_squares
-- name    : GRH.centered_moebius_bound_iff_lower_bound_at_squares
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T20:55:31.87845+00:00
-- url     : https://prove2.me/theorems/01ba592c-05d9-4f27-b8e9-106bbeae4329
-- title:
--   Lower bounds for the centered progression sum at squares suffice for full cancellation
-- statement:
--   The full centered Möbius estimate is equivalent to a lower estimate alone for the same centered sums at perfect squares, with a separate constant for every modulus, unit residue and exponent strictly between one half and one.
-- source:
--   Arithmetic reduction of the exact centered progression estimate. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 The signed remainder identity controls the sum at a perfect square. https://prove2.me/theorems/99bde901-b30d-40ce-ae0f-029719b78029

import Definitions.Def_GRH_OneSidedMoebius

open MeasureTheory Set GRH.OneSidedMoebius

theorem GRH.centered_moebius_bound_iff_lower_bound_at_squares : centeredBound ↔
    ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a → ∀ σ : ℝ, 1/2 < σ → σ < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ,
        -(C*((u:ℝ)^2+1)^σ) ≤ GRH.centeredMoebiusBilinear q a (u^2) := by sorry
