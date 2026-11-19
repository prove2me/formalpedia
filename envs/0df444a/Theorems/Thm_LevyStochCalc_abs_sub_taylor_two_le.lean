-- Prove2me | Theorems.Thm_LevyStochCalc_abs_sub_taylor_two_le
-- name    : LevyStochCalc.abs_sub_taylor_two_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:42:21.276762+00:00
-- url     : https://prove2.me/theorems/6d1f1b97-26db-4a94-b3c1-6f87cf3f7a26
-- title:
--   abs sub taylor two le
-- statement:
--   The source theorem `LevyStochCalc.abs_sub_taylor_two_le` is extracted from `LevyStochCalc.Brownian.TaylorTwo`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_TaylorTwo_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Second-order Taylor bound with a Lipschitz second derivative

For a twice-differentiable real function whose second derivative is `K`-Lipschitz, the
second-order Taylor polynomial approximates the function to within `K|y − x|³`.

## Main statements

* `LevyStochCalc.abs_sub_taylor_one_le` — the first-order Taylor remainder bound.
* `LevyStochCalc.abs_sub_taylor_two_le` — the second-order Taylor remainder bound.
* `LevyStochCalc.abs_sub_sum_taylor_two_le` — the telescoped form along a sequence.
* `LevyStochCalc.taylorRemainder` — the telescoped remainder as a function of the sequence.
* `LevyStochCalc.abs_taylorRemainder_le` — its bound.
-/

namespace LevyStochCalc

theorem _root_.LevyStochCalc.abs_sub_taylor_two_le {f f' f'' : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf'' : ∀ u v : ℝ, |f'' u - f'' v| ≤ K * |u - v|) (x y : ℝ) :
    |f y - f x - f' x * (y - x) - f'' x * (y - x) ^ 2 / 2| ≤ K * |y - x| ^ 3 := by sorry
