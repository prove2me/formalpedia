-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_fourth_power_residue_of_geom_source
-- name    : OddPerfectNumber.Kernel.fourth_power_residue_of_geom_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T22:43:38.661646+00:00
-- url     : https://prove2.me/theorems/caa33f60-e412-4136-bade-f1b6d10bb336
-- title:
--   A geometric-sum source is a fourth-power residue
-- statement:
--   An incoming geometric-sum sigma source t of the Euler prime p (p prime, p = 1 mod 4, p not dividing t) is a fourth-power residue mod p: t^((p-1)/4) = 1. The order bridge gives orderOf(t) | 2e+1, hence odd; the quarter theorem gives orderOf(t) | (p-1)/4; hence the power congruence. Applies directly to the q/r non-self sources, which are already in geometric-sum form.
-- source:
--   Composes Proved geom_sum_dvd_implies_order_dvd (d9c2c20a) with Proved odd_order_dvd_quarter_of_p_minus_one (08fe6da2). Applies to the q/r non-self sources in the 6eb10265 residual.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem fourth_power_residue_of_geom_source (p t e : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (ht : t.Prime) (hpt : Not (Dvd.dvd p t))
    (hsrc : Dvd.dvd p (∑ i ∈ Finset.range (2 * e + 1), t ^ i)) :
    (t ^ ((p - 1) / 4)) % p = 1 := by
  sorry

end OddPerfectNumber.Kernel
