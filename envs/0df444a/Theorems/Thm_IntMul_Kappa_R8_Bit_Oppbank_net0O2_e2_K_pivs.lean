-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e2_K_pivs
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_e2_K_pivs
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:12:45.386119+00:00
-- url     : https://prove2.me/theorems/f7c8a01b-b804-43f2-bcba-114fbab4866e
-- title:
--   Origin pivots of e2 residual
-- statement:
--   Origin-diagonal $\mathrm{IsPiv}$ for the stage-two residual, $0\le k<\mathrm{rkC}(o,c)$.
--
--   **Formalization Note.** Pair of `net0O2_e1_K_pivs`.
-- source:
--   supports net0O2_e2_PE_pos

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem net0O2_e2_K_pivs (a o c : ℕ) (ha : a < v) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    ∀ k, k < rkC o c → IsPiv (K S0 Si0 (Pl a) (Dm o c)) k k := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
