-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cutoffPredictableIntegrandSquareBoundV1
-- name    : Kyprianou.Ch04.cutoffPredictableIntegrandSquareBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:12:33.796484+00:00
-- url     : https://prove2.me/theorems/f64bf243-2a18-4b8d-91f4-574a753ef048
-- title:
--   Pointwise square bound for nested predictable small-jump integrands
-- statement:
--   For a bounded differentiable spatial derivative with bounded derivative, the square of the nested-cutoff weighted-mark difference is bounded by the disjoint-band quadratic mass plus the common-band squared state difference. The mean value theorem gives the Lipschitz factor. This is the pointwise inequality in Exercise 4.5(ii).
-- source:
--   Kyprianou (2006), Exercise 4.5(ii), pp. 107–108

import Mathlib
open Set
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem cutoffPredictableIntegrandSquareBoundV1 (g : ℝ → ℝ) (K ε η x y z : ℝ)
    (_hK : 0 ≤ K) (hηε : η < ε)
    (hb : ∀ u, |g u| ≤ K)
    (hg : Differentiable ℝ g) (hd : ∀ u, |deriv g u| ≤ K) :
    (({w : ℝ | η < |w| ∧ |w| < 1}).indicator
        (fun w => w * g x) z -
      ({w : ℝ | ε < |w| ∧ |w| < 1}).indicator
        (fun w => w * g y) z) ^ 2 ≤
    K ^ 2 * (({w : ℝ | η < |w| ∧ |w| ≤ ε ∧ |w| < 1}).indicator
        (fun w => w ^ 2) z +
      ({w : ℝ | ε < |w| ∧ |w| < 1}).indicator
        (fun w => w ^ 2 * (x - y) ^ 2) z) := by
  sorry
end Kyprianou.Ch04
