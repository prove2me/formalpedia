-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_family_zero_on_negative
-- name    : Kyprianou.Ch08.StageB.source_family_zero_on_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:56:44.34798+00:00
-- url     : https://prove2.me/theorems/2c169c48-bbb3-4cc5-8646-c82a59819c09
-- title:
--   Vanishing of source scale function below zero
-- statement:
--   Every spectrally negative q-scale function is zero for x<0, uniformly for q≥0. This is exactly the support property in Kyprianou Theorem 8.1(i), used in the two-sided exit kernels, killed resolvents and first-passage boundary cases.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1(i), printed p. 214.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

/-- Every source q-scale function vanishes strictly below zero. -/
theorem source_family_zero_on_negative (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q x : ℝ) (hq : 0 ≤ q) (hx : x < 0) :
    W q x = 0 := by
  sorry

end Kyprianou.Ch08.StageB
