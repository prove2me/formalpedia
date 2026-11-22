-- Prove2me | Theorems.Thm_GradientAnnulus
-- name    : GradientAnnulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:11:31.362187+00:00
-- url     : https://prove2.me/theorems/09fd9ee4-6c59-485c-b43b-be552e4ee2b5
-- title:
--   Gradient Annulus: Gradient Annulus
-- statement:
--   The first step of the paper's proof of lem:noncritical (paper lines 166-170): a radius
--   `tau ∈ (0, 1/4)`, depending only on `p` and `delta` through the Lewis-Tolksdorf data
--   `kappa, C₀`, on whose doubled ball the gradient of every normalized `p`-harmonic function
--   with `|Dv(0)| > delta` is trapped in the annulus `delta/2 ≤ |Dv| ≤ C₀`.
--
--   The paper's choice is `C₀ (2 tau)^kappa ≤ delta/2`: the `kappa`-Holder estimate of
--   eq:first then moves `Dv` by at most `delta/2` across `ball 0 (2 tau)`, so it can neither
--   reach `0` nor leave the ball of radius `C₀`.
--
--   The third conjunct, `‖Dv x - Dv 0‖ ≤ delta/2`, records that displacement bound itself and is
--   what the Schauder bootstrap actually needs: it says the RANGE of `Dv` on `ball 0 (2 tau)` lies
--   in the closed ball of radius `delta/2` about `Dv 0`, a CONVEX set which avoids the origin
--   because `delta < ‖Dv 0‖`.  The annulus `delta/2 ≤ ‖xi‖ ≤ C₀` of the first two conjuncts is not
--   convex, so the mean value inequality cannot be applied along a segment joining two values of
--   `Dv` using it alone.
--
--   The quantifier order is the one the paper's uniformity requires and the one pm-0005 is
--   about: `tau` is produced BEFORE `v`, from `p` and `delta` alone.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/GradientAnnulus.lean#L21-L90
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/GradientAnnulus.lean#L21-L90

import Definitions.Def_PHigherOrder_FirstOrderEstimateInput
import Definitions.Def_PHigherOrder_GradientAnnulus
set_option autoImplicit false

theorem GradientAnnulus (p : ℝ) (F : FirstOrderEstimateInput p) (δ : ℝ) (hδ : 0 < δ) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 / 4 ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
        (∀ x ∈ Metric.ball (0 : Plane) 1, |v x| ≤ 1) → δ < ‖gradient v 0‖ →
        ContDiffOn ℝ 1 v (Metric.ball 0 (2 * τ)) ∧
          ∀ x ∈ Metric.ball (0 : Plane) (2 * τ),
            δ / 2 ≤ ‖gradient v x‖ ∧ ‖gradient v x‖ ≤ F.C₀
              ∧ ‖gradient v x - gradient v 0‖ ≤ δ / 2 := by sorry
