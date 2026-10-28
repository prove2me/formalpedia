-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_good_primes_edges
-- name    : IntMul.Kappa.R8.Bit.Oppbank.good_primes_edges
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:07:45.033752+00:00
-- url     : https://prove2.me/theorems/0a350184-125f-4e7e-ab4e-8f0d00bcbea3
-- title:
--   R8 Oppbank RunsOK ∧ EdgesOK for net0P
-- statement:
--   The densified opp-bank network $\mathrm{net0P}$ is $\mathrm{RunsOK}$, and there exists $q_0$ such that for every prime $q>q_0$ and every $f$, $\mathrm{EdgesOK}(\mathrm{net0P},q^f)$. This is the EdgesOK half of $\mathrm{good\_primes}$ / $\mathrm{net0\_ok}$.
-- source:
--   GoodPrimesEdges net0_runs_edges.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGoodPrimes
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0P
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGoodPrimesEdges
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.QHNet (RunsOK EdgesOK)
open IntMul.Kappa.R8.Bit.Oppbank.Net0P

theorem good_primes_edges :
    ∃ q₀ : ℕ,
      RunsOK (m := 529) net0P ∧
        (∀ q, q.Prime → q₀ < q → ∀ f, EdgesOK (m := 529) net0P (q ^ f)) := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
