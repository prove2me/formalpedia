-- Prove2me | Theorems.Thm_OddPerfectNumber_local_val_eq_of_mod_one
-- name    : OddPerfectNumber.local_val_eq_of_mod_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T10:23:51.656973+00:00
-- url     : https://prove2.me/theorems/44d3cead-fbfb-440e-9b9f-6e954480e396
-- title:
--   Local valuation collapses in the 1-mod-p branch
-- statement:
--   If the prime $q$ is $1$ modulo the odd prime $p$, then the $p$-adic valuation of the local geometric sum $1 + q + \cdots + q^{2e}$ equals the $p$-adic valuation of the length $2e+1$. The sum times $q - 1$ is $q^{2e+1} - 1$ (telescoping), LTE splits its valuation, and the $q - 1$ part cancels. This is the $1$-mod-$p$ branch of the order analysis on the $k = 1$ distinguished prime.
-- source:
--   Valuation-flow analysis of the Odd Perfect Number Conjecture; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem local_val_eq_of_mod_one (p q e : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq1 : p ∣ q - 1) :
    padicValNat p (∑ i ∈ Finset.range (2 * e + 1), q ^ i)
      = padicValNat p (2 * e + 1) := by
  sorry

end OddPerfectNumber
