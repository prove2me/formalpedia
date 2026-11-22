-- Prove2me | Theorems.Thm_JetBounds
-- name    : JetBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:04:00.717574+00:00
-- url     : https://prove2.me/theorems/2550d9e2-576f-4595-89af-12cf5ae0b2dd
-- title:
--   Jet Bounds: Jet Bounds
-- statement:
--   Paper eq:jet-bound and eq:jet-error (paper lines 283-303): the jets of a `p`-harmonic
--   `u ∈ L^p(B_1)` at any point of `B_{1/2}` are bounded by its `L^p` norm, and its degree-`k`
--   Taylor polynomial at that point approximates it to order `sigma = k + beta` on the quarter ball
--   around it.
--
--   Route, following the paper.  `LocalBoundednessInput` bounds `|u|` on `B_{3/4}` by
--   `C_b ‖u‖_{L^p(B_1)}`; the paper's normalizing constant is `M_0 = 2 C_b ‖u‖_{L^p(B_1)}`, and the
--   factor `2` is what makes `|w_x| ≤ 1` below come out, so it must not be dropped.  For
--   `x ∈ B_{1/2}` the rescaled function `w_x y = (u (x + y/4) - u x)/M_0` is `p`-harmonic on `B_1`
--   by `PHarmNormalize` with `r = 1/4`, `c = u x`, `M = M_0`, cut down by `PHarmRestrict`, vanishes
--   at `0`, and is bounded by `1` there; so `Approximation` applies, uniformly in `x` because its
--   constant is produced before the function.  `TaylorPolyAffine` then transports both conclusions
--   back: clause (1) at `r = 1/4` carries the factor `4^j ≤ 4^k` into the constant, and clause (2)
--   is literally the paper's `P_x(z) = u(x) + M_0 Q_x(4(z-x))`, so that
--   `u z - TaylorPoly k u x z = M_0 (w_x y - TaylorPoly k w_x 0 y)` at `y = 4 • (z - x)`, where
--   `‖y‖ = 4‖z - x‖ < 1` exactly when `z ∈ ball x (1/4)` — which is why `Approximation`'s error
--   clause had to be POINTWISE in the norm.
--
--   Both conclusions are stated in terms of `‖u‖_{L^p(B_1)}` rather than `M_0 = 2 C_b
--   ‖u‖_{L^p(B_1)}`; the factor `2 C_b` depends only on `p` and is absorbed into `C`, which is the
--   paper's own bookkeeping ("all constants depend only on `p, k, beta`").  The case
--   `‖u‖_{L^p(B_1)} = 0`, i.e. `M_0 = 0`, is real and not vacuous, and is handled separately: `u`
--   then vanishes on `B_{3/4}` by local boundedness, so every jet of order `≥ 1` vanishes at `x` and
--   both sides of both conclusions are zero.
--
--   Everything is diagonal, and the full operator norm of `iteratedFDeriv ℝ j u x` is deliberately
--   never used.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/JetBounds.lean#L34-L215
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/JetBounds.lean#L34-L215

import Definitions.Def_PHigherOrder_Approximation
import Definitions.Def_PHigherOrder_LocalBoundednessInput
import Definitions.Def_PHigherOrder_PHarmNormalize
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_TaylorPolyAffine
import Definitions.Def_PHigherOrder_JetBounds
import Theorems.Thm_Approximation
import Theorems.Thm_PHarmNormalize
import Theorems.Thm_PHarmRestrict
import Theorems.Thm_TaylorPolyAffine

set_option autoImplicit false

theorem JetBounds (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hLR : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (hsm : SmoothAwayFromCriticalInput p) (hS : DivFormSchauderInput)
    (hLB : LocalBoundednessInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) u g →
        MeasureTheory.MemLp u (ENNReal.ofReal p)
          (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1)) →
        ∀ x ∈ Metric.ball (0 : Plane) (1 / 2),
          (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ w : Plane,
              |iteratedFDeriv ℝ j u x (fun _ => w)|
                ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                      (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                  * ‖w‖ ^ j)
            ∧ (∀ z ∈ Metric.ball x (1 / 4),
                |u z - TaylorPoly k u x z|
                  ≤ C * (MeasureTheory.eLpNorm u (ENNReal.ofReal p)
                        (MeasureTheory.volume.restrict (Metric.ball (0 : Plane) 1))).toReal
                    * ‖z - x‖ ^ ((k : ℝ) + β)) := by sorry
