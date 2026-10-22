-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0_ok
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0_ok
-- status  : Open
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:35:12.113798+00:00
-- url     : https://prove2.me/theorems/17856c66-776d-4451-9a2f-a3fd5c7c778f
-- title:
--   R8 densified net0P is RunsOK and EdgesOK/FormalOK for large primes
-- statement:
--   Let $\mathrm{net0P}$ be the densified opp-bank QH-network of width $m=529$ on $W=104719230$ roles (published `Net0P`, with honest `Pnd` ND projectors available via `BitOppbankPnd`). There exists a bound $q_0$ such that $\mathrm{RunsOK}(\mathrm{net0P})$ holds, and for every prime $q>q_0$ and every $f$, both $\mathrm{EdgesOK}$ and $\mathrm{FormalOK}$ hold at the prime power $q^f$.
--
--   The `RunsOK` half is already proved in `GoodPrimes` via a finite edge family $E_0$ and `EdgeQ`. The remaining half is the Defs52 `good_primes` retarget at $\mathrm{codeBound}=64251$, using NetFB Lab0 certificates and densified `Pnd`/`HasCentre`.
-- source:
--   GoodPrimes fac3e30f; NetFB cb08d016; Pnd 1351eb81; Net0P 373d80bb; Defs52 net0_ok

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0P
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGoodPrimes
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.QHNet (RunsOK EdgesOK FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank.Net0P

/-- Densified opp-bank network `net0P` is RunsOK and EdgesOK/FormalOK above a prime bound. -/
theorem net0_ok :
    ∃ q₀ : ℕ,
      RunsOK (m := 529) net0P ∧
        (∀ q, q.Prime → q₀ < q → ∀ f,
          EdgesOK (m := 529) net0P (q ^ f) ∧ FormalOK (m := 529) net0P (q ^ f)) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
