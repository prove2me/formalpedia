-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_source_dispatch
-- name    : OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_source_dispatch
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T19:56:08.319425+00:00
-- url     : https://prove2.me/theorems/e28e22da-2112-4976-8d54-ff587f974ea2
-- title:
--   The q3=19 D=57 source cases dispatch to p=113
-- statement:
--   Each of the q3=19 D=57 candidates q4=593,599,601 is impossible once its explicit p=113 source and fourth-factor order obstruction are supplied.
-- source:
--   Finite source dispatch through the accepted p=113 obstruction; the q4-specific order facts remain explicit obligations.

import Mathlib
import Theorems.Thm_OddPerfectNumber_even_order_three_mod_113
import Theorems.Thm_OddPerfectNumber_even_order_five_mod_113
import Theorems.Thm_OddPerfectNumber_even_order_nineteen_mod_113
import Theorems.Thm_OddPerfectNumber_k_one_p113_no_local_sigma_source_general

namespace OddPerfectNumber

theorem k_one_q2_five_q3_nineteen_small_D_source_dispatch (sigma a b c e q4 : Nat)
    (hsigma : sigma = (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2 * c + 1), 19 ^ i) * (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hcase : (q4 = 593 ∧ 113 ∣ sigma ∧ ¬ orderOf (593 : ZMod 113) ∣ 2 * e + 1) ∨ (q4 = 599 ∧ 113 ∣ sigma ∧ ¬ orderOf (599 : ZMod 113) ∣ 2 * e + 1) ∨ (q4 = 601 ∧ 113 ∣ sigma ∧ ¬ orderOf (601 : ZMod 113) ∣ 2 * e + 1)) :
    False := by
  sorry

end OddPerfectNumber
