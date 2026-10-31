-- Prove2me | Theorems.Thm_OddGoldbach19_circle_cosecant_bound_five
-- name    : OddGoldbach19.circle_cosecant_bound_five
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:42:46.044995+00:00
-- url     : https://prove2.me/theorems/0c1c3688-420e-4911-be94-9a5de66ee7ca
-- title:
--   Circle Hilbert bound with constant five
-- statement:
--   For every finite family of real frequencies theta_r and complex coefficients v_r with circular gaps delta_r positive and at most1, assume delta_r <= |theta_r-theta_s+m| for all distinct r,s and all integers m. Then the norm of the off-diagonal sum v_r*conj(v_s)/sin(pi*(theta_r-theta_s)) is at most5 times the sum of |v_r|^2/delta_r. This improves the previously proved constant16 under the same hypotheses.
-- source:
--   Derived refinement of existing public Prove2Me weighted Hilbert and pair-sieve proof chain; see proof explanation for precise reused accepted submission IDs.

import Mathlib
open scoped BigOperators ComplexConjugate

theorem OddGoldbach19.circle_cosecant_bound_five {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ δ : ι → ℝ) (v : ι → ℂ)
    (hpos : ∀ r, 0 < δ r) (hunit : ∀ r, δ r ≤ 1)
    (hgap : ∀ r s, r ≠ s → ∀ m : ℤ, δ r ≤ |θ r - θ s + m|) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else
      v r * conj (v s) /
        Complex.sin ((Real.pi : ℂ) * ((θ r - θ s : ℝ) : ℂ))‖ ≤
      5 * ∑ r, ‖v r‖ ^ 2 / δ r := by sorry
