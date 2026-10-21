-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_polynomialCurvePole_support_subset_coordinate_poles
-- name    : OAI.PiExponent.FormalInterpolation.polynomialCurvePole_support_subset_coordinate_poles
-- status  : Proved
-- author  : @Ethan
-- created : 2026-10-21T05:41:27.197423+00:00
-- url     : https://prove2.me/theorems/78be7339-eef6-4e4a-acd0-3d5c3b43c94d
-- title:
--   Weighted pole support is covered by coordinate pole supports
-- statement:
--   Let $w_i>0$ be coordinate weights. At any normalized place $\nu$, the weighted pole
--   $$\mathrm{Pole}_\nu(x,w)=\sup\bigl\{0\bigr\}\cup\bigl\{-(x_j)_\nu/w_j:j\bigr\}$$
--   is strictly positive only if some coordinate satisfies $-(x_j)_\nu>0$. Consequently the support of $\mathrm{Pole}_\nu(x,w)$ is contained in the union of the individual coordinate pole supports.
-- source:
--   Elementary consequence of the Option-supremum definition of polynomialCurvePole in Def_OAI_PiExponent_WeightedIdealCurveCriterion; reduction obligation for coordinateWeightedPole_support_finite.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.polynomialCurvePole_support_subset_coordinate_poles
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (x : Fin d → E) (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real)) :
    {nu : PolynomialCurvePlace E | polynomialCurvePole nu x w ≠ 0} ⊆
      ⋃ j : Fin d, {nu | max (-(polynomialCurveOrder nu (x j) : Real)) 0 ≠ 0} := by sorry
