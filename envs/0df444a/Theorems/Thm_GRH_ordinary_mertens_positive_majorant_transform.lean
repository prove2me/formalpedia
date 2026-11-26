-- Prove2me | Theorems.Thm_GRH_ordinary_mertens_positive_majorant_transform
-- name    : GRH.ordinary_mertens_positive_majorant_transform
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T20:55:31.550185+00:00
-- url     : https://prove2.me/theorems/58648391-6fff-5341-9b5c-cbb36c22a9d5
-- title:
--   Mellin transform of a power majorant minus the Mertens sum
-- statement:
--   Let A(x) = D x^θ − M(floor x), with D nonnegative and θ below one. The function is measurable, its weighted integral converges at every real exponent above one, and its Mellin transform for Re s greater than one is D/(s−θ) − 1/(s ζ(s)).
-- source:
--   Arithmetic reduction of the exact centered progression estimate. https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 The initial identity uses the pinned Mathlib L-series integral and the Möbius inverse of the zeta series.

import Definitions.Def_GRH_OneSidedMoebius

open MeasureTheory Set GRH.OneSidedMoebius

theorem GRH.ordinary_mertens_positive_majorant_transform (D θ : ℝ) (hD : 0 ≤ D) (hθ : θ < 1) :
    Measurable (majorant D θ) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => majorant D θ x * x^(-σ-1)) (Set.Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re → transform (majorant D θ) s =
      (D : ℂ)/(s-θ) - (s*riemannZeta s)⁻¹ := by sorry
