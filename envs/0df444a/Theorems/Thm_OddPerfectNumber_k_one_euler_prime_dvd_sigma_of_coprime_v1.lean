-- Prove2me | Theorems.Thm_OddPerfectNumber_k_one_euler_prime_dvd_sigma_of_coprime_v1
-- name    : OddPerfectNumber.k_one_euler_prime_dvd_sigma_of_coprime_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T14:46:55.675751+00:00
-- url     : https://prove2.me/theorems/e17f8aae-fc77-45ae-84b1-48bc1a519fc8
-- title:
--   Euler prime divides sigma from deficient relation
-- statement:
--   From D*sigma=p*m^2 with p=2D-1 prime and D>1, the Euler prime is coprime to D and hence divides sigma.

import Mathlib

namespace OddPerfectNumber

theorem k_one_euler_prime_dvd_sigma_of_coprime_v1 (m D p sigma : Nat)
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1) (hp : p.Prime)
    (hD : 1 < D) :
    p ∣ sigma := by
  sorry

end OddPerfectNumber
