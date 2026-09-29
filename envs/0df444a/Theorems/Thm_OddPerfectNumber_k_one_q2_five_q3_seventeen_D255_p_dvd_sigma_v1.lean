-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D255_p_dvd_sigma_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_D255_p_dvd_sigma_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T14:39:30.142853+00:00
-- url     : https://prove2.me/theorems/fdca532f-d738-461a-b4ff-092a24148ce0
-- title:
--   q17 D255 Euler prime divides sigma
-- statement:
--   From D=255, p=2D-1 prime and D*sigma=p*m^2, the Euler prime divides sigma since it is coprime to D.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_D255_p_dvd_sigma_v1 (m D p sigma : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hD : D = 255) :
    p ∣ sigma := by
  sorry

end OddPerfectNumber
