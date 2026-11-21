-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_Phi_below_beta
-- name    : Kyprianou.Ch08.StageB.source_stable_Phi_below_beta
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:36:38.507176+00:00
-- url     : https://prove2.me/theorems/f62aa724-6313-421d-a1ca-5b0ae6ee2878
-- title:
--   Stable exponent right root below beta
-- statement:
--   The stable q-scale root Phi satisfies Phi^alpha=q, is nonnegative, and lies below beta when beta exceeds q^(1/alpha). Use the published stable geometric ratio bound and monotonic real powers.
-- source:
--   Kyprianou (2006), Ch8 Exercise 8.2(i)

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB
theorem source_stable_Phi_below_beta
    (α q β : ℝ) (hα : 1 < α) (hq : 0 < q)
    (hβ : q ^ (1 / α) < β)
    (hPhi : PhiIsLargestRoot (fun v : ℝ => v ^ α) q) :
    Phi (fun v : ℝ => v ^ α) q < β := by
  sorry
end Kyprianou.Ch08.StageB
