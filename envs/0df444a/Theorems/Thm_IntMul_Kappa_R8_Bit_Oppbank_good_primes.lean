-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_good_primes
-- name    : IntMul.Kappa.R8.Bit.Oppbank.good_primes
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:04:44.14207+00:00
-- url     : https://prove2.me/theorems/e7262c43-e9b0-4adc-a052-4dda720fe3d1
-- title:
--   R8 Oppbank good_primes at codeBound=64251
-- statement:
--   There exists a bound $q_0$ such that for every prime $q>q_0$ and every $f$, every edge in the densified finite family $E_0$ is $\mathrm{EdgeOK}$ at $q^f$, and $\mathrm{FormalOK}(\mathrm{net0P},q^f)$ holds. This is the Defs52 `good_primes` retarget used by `net0_ok`; the EdgeOK half follows from R6 `good_edges` once $E_0$/$E_0\_Q$ are in place (GoodPrimes), while FormalOK needs full $\mathrm{FB0\_ex}$/$\mathrm{EOK}$.
-- source:
--   R6 Defs52; R8 GoodPrimes; FB0_ex_Pl 7f4c81df.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGoodPrimes
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0P
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.QHNet (FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank.GoodPrimes
open IntMul.Kappa.R8.Bit.Oppbank.Net0P

/-- Densified good_primes: EdgeOK on E0 and FormalOK(net0P) above a prime bound. -/
theorem good_primes :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ,
      (∀ e ∈ GoodPrimes.E0, EdgeOK (q ^ f) e) ∧
        FormalOK (m := 529) net0P (q ^ f) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
