-- Prove2me | Theorems.Thm_O3_scale_geometric_sum_le_endpoint
-- name    : O3.scale_geometric_sum_le_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:30.36699+00:00
-- url     : https://prove2.me/theorems/75d8b038-f37e-598b-899b-6838b2780074
-- title:
--   O3: scale geometric sum le endpoint
-- statement:
--   The same genuine geometric sum across scale epochs.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean#L83-L87
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean#L83-L87

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization
set_option autoImplicit true
open O3

theorem O3.scale_geometric_sum_le_endpoint {a k0 : ℝ}
    (ha : 0 < a) (hk0 : 0 ≤ k0) (S : ℕ) :
    ∑ s ∈ Finset.range (S + 1), (((2 : ℝ) ^ s * k0) ^ a) ≤
      geometricAmortizationConstant a * (((2 : ℝ) ^ S * k0) ^ a) := by sorry
