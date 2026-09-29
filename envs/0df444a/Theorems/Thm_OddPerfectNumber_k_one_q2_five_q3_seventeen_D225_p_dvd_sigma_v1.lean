-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_seventeen_D225_p_dvd_sigma_v1
-- name    : OddPerfectNumber.k_one_q2_five_q3_seventeen_D225_p_dvd_sigma_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T14:35:08.497775+00:00
-- url     : https://prove2.me/theorems/4fcf8ecc-dfa5-4147-9beb-e2026a286a80
-- title:
--   q17 D225 Euler prime divides sigma
-- statement:
--   From D=225, p=2D-1 prime and D*sigma=p*m^2, the Euler prime divides sigma since it is coprime to D.

import Mathlib

namespace OddPerfectNumber

theorem k_one_q2_five_q3_seventeen_D225_p_dvd_sigma_v1 (m D p sigma : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hD : D = 225) :
    p ∣ sigma := by
  sorry

end OddPerfectNumber
