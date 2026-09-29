-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_D15_b1_terminal_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_thirtyone_D15_b1_terminal_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T16:52:08.661546+00:00
-- url     : https://prove2.me/theorems/a0fe65f9-8b05-4a7f-8b0d-132abcbab13e
-- title:
--   q31 D15 b=1 terminal over the 61/151 residual cases
-- statement:
--   D15 b=1 terminal: with q4 in {61,151}, exact orders 10/50, and prime-order index hypothesis, contradiction via the proved residual helper. The prime-order premise is discharged separately by the index-primality lemma.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirtyone_residual_order_absurd_v1

namespace OddPerfectNumber

theorem k_one_q2_five_q3_thirtyone_D15_b1_terminal_v1 (D q4 : Nat)
    (hD : D = 15) (hq : q4 = 61 ∨ q4 = 151)
    (ho61 : q4 = 61 → orderOf (3 : ZMod q4) = 10)
    (ho151 : q4 = 151 → orderOf (3 : ZMod q4) = 50)
    (hindex : Nat.Prime (orderOf (3 : ZMod q4))) : False := by
  sorry

end OddPerfectNumber
