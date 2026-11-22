-- Prove2me | Theorems.Thm_HolderFromJets
-- name    : HolderFromJets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:12:17.783184+00:00
-- url     : https://prove2.me/theorems/de97f09a-4b19-4c30-abc1-ee6d5c498b0d
-- title:
--   Holder From Jets: Holder From Jets
-- statement:
--   The Holder seminorm term of paper eq:main (paper lines 305-313): the order-`k` jets of a
--   `p`-harmonic `u ∈ L^p(B_1)` are `beta`-Holder on `B_{1/2}`, with constant a multiple of
--   `‖u‖_{L^p(B_1)}`.
--
--   Route, following the paper.  For distinct `x, y ∈ B_{1/2}` put `d = ‖x - y‖`.  If `d < 1/16`
--   then `ball x d` sits inside both `ball x (1/4)` and `ball y (1/4)`, because
--   `‖z - y‖ < 2d < 1/4` for `z ∈ ball x d`; so both of `JetBounds`'s error bounds hold there and
--   the two Taylor polynomials are uniformly close on `ball x d`, to order `d^sigma` — the
--   `y`-centred bound on the larger radius `2d`, whose factor `2^sigma` is absorbed into the
--   constant.  `PolyInverseEstimate`, applied to their DIFFERENCE at the common centre `x`, then
--   converts closeness into a bound on the order-`k` derivative, with the factor `d^(-k)` that
--   turns `d^sigma` into `d^beta` since `sigma = k + beta`.  The two polynomials are differentiated
--   at the SAME point `x`, which is legitimate because clause (3) of `TaylorPolyDeriv` identifies
--   the order-`k` diagonal evaluation of a Taylor polynomial with that of its function at EVERY
--   point, not only at the centre.  If `d ≥ 1/16` the bound follows from `JetBounds`'s jet bound
--   alone, since `d^beta ≥ 16^(-beta)`.
--
--   The conclusion is the two-point DIAGONAL form.  The full operator norm of
--   `iteratedFDeriv ℝ k u x` is never used, and no symmetry or polarization of the derivative
--   tensor is developed: `PolyInverseEstimate` is the one place a full operator norm appears, and
--   there it is the norm of a derivative of a POLYNOMIAL.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/HolderFromJets.lean#L26-L193
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/HolderFromJets.lean#L26-L193

import Definitions.Def_PHigherOrder_JetBounds
import Definitions.Def_PHigherOrder_PolyInverseEstimate
import Definitions.Def_PHigherOrder_TaylorPolyDeriv
import Definitions.Def_PHigherOrder_HolderFromJets
import Theorems.Thm_JetBounds
import Theorems.Thm_PolyInverseEstimate
import Theorems.Thm_TaylorPolyDeriv

set_option autoImplicit false

theorem HolderFromJets (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hLR : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (hsm : SmoothAwayFromCriticalInput p) (hS : DivFormSchauderInput)
    (hLB : LocalBoundednessInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) u g →
        MeasureTheory.MemLp u (ENNReal.ofReal p)
          (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1)) →
        ∀ x ∈ Metric.ball (0 : Plane) (1 / 2), ∀ y ∈ Metric.ball (0 : Plane) (1 / 2),
          ∀ w : Plane,
            |iteratedFDeriv ℝ k u x (fun _ => w) - iteratedFDeriv ℝ k u y (fun _ => w)|
              ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                    (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                * ‖x - y‖ ^ β * ‖w‖ ^ k := by sorry
