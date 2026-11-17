-- Prove2me | Theorems.Thm_Height_exists_logHeight_le_restrict_add_of_bezout
-- name    : Height.exists_logHeight_le_restrict_add_of_bezout
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:21:32.596467+00:00
-- url     : https://prove2.me/theorems/64e557fd-3c18-4a9d-8de8-6fecdfed7c8b
-- title:
--   Height comparison from a homogeneous Bezout certificate
-- statement:
--   If every coordinate z_k satisfies z_k^(D+1) = sum_j q_(k,j)(z) z_(inc j) with q homogeneous of degree D, then the logarithmic height of z is at most that of its restriction z o inc plus a constant independent of z.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib

set_option autoImplicit false

namespace Height
theorem exists_logHeight_le_restrict_add_of_bezout {K : Type} [Field K] [NumberField K] {ι ι' : Type}
    [Finite ι] [Fintype ι'] [Nonempty ι'] (inc : ι' → ι) {D : ℕ}
    (q : ι × ι' → MvPolynomial ι K) (hq : ∀ a, (q a).IsHomogeneous D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ι → K,
      (∀ k, ∑ j, (q (k, j)).eval z * z (inc j) = z k ^ (D + 1)) →
      Height.logHeight z ≤ Height.logHeight (z ∘ inc) + C := by sorry
end Height
