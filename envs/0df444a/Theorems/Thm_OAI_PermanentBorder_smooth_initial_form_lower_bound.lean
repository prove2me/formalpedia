-- Prove2me | Theorems.Thm_OAI_PermanentBorder_smooth_initial_form_lower_bound
-- name    : OAI.PermanentBorder.smooth_initial_form_lower_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:03.006364+00:00
-- url     : https://prove2.me/theorems/67355e9f-c33a-429d-b121-92775d59b558
-- statement:
--   The theorem states that, for natural numbers d ≥ 2 and r ≥ 2, a complex polynomial g in d variables, and a point a ∈ ℂ^d, suppose the translated polynomial h(x) = g(a + x) (obtained by the affine substitution x_i ↦ a_i + x_i, with identity linear part) has all homogeneous components of degree below r equal to zero and nonzero degree-r component h_r, so the lowest-degree part of g at a has degree exactly r. Suppose also that h_r is smooth in the sense that any y ∈ ℂ^d at which h_r and all its partial derivatives vanish must be y = 0. Then for every n, if g is a border determinant of size n, meaning n > 0 and there are sequences of n×n matrices A₀(j) and A_v(j) (one for each variable v) such that the determinant of A₀(j) + Σ_v x_v A_v(j) has every coefficient converging to the corresponding coefficient of g as j → ∞, then (r−1)(d−1)/(4e) ≤ n; and likewise, if g is exactly the determinant of an n×n matrix of affine-linear forms A₀ + Σ_v x_v A_v with n > 0, then (r−1)(d−1)/(4e) ≤ n, where e is Euler's number.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SmoothInitialForm.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SmoothInitialForm.lean; bytes 1256..2217
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SmoothInitialForm

namespace OAI

open MvPolynomial

namespace PermanentBorder

open Filter

open scoped Topology

theorem smooth_initial_form_lower_bound (d r : ℕ) (g : Poly (Fin d))
    (a : Fin d → ℂ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hG : homogeneousComponent r
      (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g) ≠ 0)
    (hlow : ∀ j < r, homogeneousComponent j
      (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g) = 0)
    (hs : ∀ y : Fin d → ℂ,
      eval y (homogeneousComponent r
        (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g)) = 0 →
      (∀ i, eval y (pderiv i (homogeneousComponent r
        (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g))) = 0) →
      y = 0) :
    ∀ n : ℕ,
      (HasBorderDeterminant n g →
        ((r - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) / (4 * Real.exp 1) ≤ (n : ℝ)) ∧
      (HasExactDeterminant n g →
        ((r - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) / (4 * Real.exp 1) ≤ (n : ℝ)) := by
  sorry

end PermanentBorder
end OAI
