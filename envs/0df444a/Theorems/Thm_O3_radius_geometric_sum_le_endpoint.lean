-- Prove2me | Theorems.Thm_O3_radius_geometric_sum_le_endpoint
-- name    : O3.radius_geometric_sum_le_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:24:19.496184+00:00
-- url     : https://prove2.me/theorems/324bf475-5a49-598b-a2bb-c00a320d8f14
-- title:
--   O3: radius geometric sum le endpoint
-- statement:
--   Exact finite inner geometric summation, expressed through its endpoint.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean#L48-L80
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean#L48-L80

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization
set_option autoImplicit true
open O3

theorem O3.radius_geometric_sum_le_endpoint {a beta : ℝ}
    (ha : 0 < a) (hbeta : 0 ≤ beta) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ j * beta) ^ a ≤
      geometricAmortizationConstant a * (((2 : ℝ) ^ J * beta) ^ a) := by sorry
