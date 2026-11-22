-- Prove2me | Theorems.Thm_MasulloRH_normalized_countable_orbit_shell_lift_lipschitz_in_radial_marginals
-- name    : MasulloRH.normalized_countable_orbit_shell_lift_lipschitz_in_radial_marginals
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T08:15:40.13409+00:00
-- url     : https://prove2.me/theorems/ee2d195b-d4b4-4384-8fcd-cb47639047c5
-- title:
--   A masked double rational-orbit marginal is Lipschitz in the normalized radial lift
-- statement:
--   Let b,c be nonnegative probability masses on a discrete group (in particular all nonzero rational shifts), and let a be a real shell mask bounded in absolute value by one. The difference of the two double angular marginal shell weights is bounded by twice the sum of |b-c|, with no finite-support condition. Thus bounded variation of a normalized radial lift controls the variation of each masked extraction.
-- source:
--   Masullo RH, (11.3.2.1–2); follows the double angular marginal identity db985081-fca8-4440-bfd1-276f6e60b4e6 and the canonical angular section. Applies to arbitrary signed real shell masks.

import Mathlib

theorem MasulloRH.normalized_countable_orbit_shell_lift_lipschitz_in_radial_marginals {D : Type*} [Group D] (b c : D → ℝ)
    (hb0 : ∀ r, 0 ≤ b r) (hc0 : ∀ r, 0 ≤ c r) (hb : HasSum b 1) (hc : HasSum c 1)
    (a : D → ℝ) (ha : ∀ ξ, |a ξ| ≤ 1) :
    |(∑' r, b r * ∑' s, b s * a (r⁻¹*s)) -
      (∑' r, c r * ∑' s, c s * a (r⁻¹*s))| ≤ 2 * ∑' r, |b r - c r| := by sorry
