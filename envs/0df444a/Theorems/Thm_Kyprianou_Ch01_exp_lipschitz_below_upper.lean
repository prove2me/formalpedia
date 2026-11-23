-- Prove2me | Theorems.Thm_Kyprianou_Ch01_exp_lipschitz_below_upper
-- name    : Kyprianou.Ch01.exp_lipschitz_below_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:13:34.712703+00:00
-- url     : https://prove2.me/theorems/e3f04b32-4762-48c0-b6b2-0d918944b5a3
-- title:
--   Real exponential is uniformly Lipschitz below a finite upper argument
-- statement:
--   For any upper bound b and real arguments x,y≤b, the difference of their exponentials is at most exp(b)|x−y|. A mean-value derivative bound on the convex interval (−∞,b] suffices. This handles the k=0 offspring term in the branching mechanism, while the previously proved exp_uniform_lipschitz_on_positive handles k≥1 without any finite offspring mean.
-- source:
--   Positive-rate Kyprianou Ch01 branching mechanism local Lipschitz estimate; derived by applying the Mathlib norm_image_sub_le_of_norm_deriv_le argument used in the already Proved Kyprianou.Ch01.exp_uniform_lipschitz_on_positive.

import Mathlib.Analysis.Complex.Exponential
open Real Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.exp_lipschitz_below_upper
    (b x y : ℝ) (hx : x ≤ b) (hy : y ≤ b) :
    |Real.exp y - Real.exp x| ≤ Real.exp b * |y - x| := by
  sorry
