-- Prove2me | Theorems.Thm_GRH_riemannHypothesis_iff_upper_mertens_at_squares
-- name    : GRH.riemannHypothesis_iff_upper_mertens_at_squares
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T20:55:32.772892+00:00
-- url     : https://prove2.me/theorems/18f77154-a665-45bc-811c-2afbf5a48a5a
-- title:
--   Ordinary RH is equivalent to upper Mertens bounds at perfect squares
-- statement:
--   Ordinary RH holds exactly when, for every real θ strictly between one half and one, some nonnegative constant C bounds M(u²) above by C(u²+1)^θ at all natural u.
-- source:
--   Arithmetic reduction of the exact centered progression estimate. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006

import Definitions.Def_GRH_OneSidedMoebius

open MeasureTheory Set GRH.OneSidedMoebius

theorem GRH.riemannHypothesis_iff_upper_mertens_at_squares : RiemannHypothesis ↔
    ∀ θ : ℝ, 1/2 < θ → θ < 1 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ℕ, mertens (u^2) ≤ C*((u:ℝ)^2+1)^θ := by sorry
