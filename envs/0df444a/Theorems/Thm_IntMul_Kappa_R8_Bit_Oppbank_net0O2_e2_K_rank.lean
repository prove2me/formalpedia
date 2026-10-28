-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e2_K_rank
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_e2_K_rank
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:12:44.619056+00:00
-- url     : https://prove2.me/theorems/8b9658b2-a1bf-4e77-b12c-05cec396d3cf
-- title:
--   Rank of e2 residual equals rkC
-- statement:
--   $\mathrm{rank}\,K(S_0,S_i,\mathrm{Pl}(a),\mathrm{Dm}(o,c))=\mathrm{rkC}(o,c)$ under positive-rank in-range hypotheses.
--
--   **Formalization Note.** Pair of `net0O2_e1_K_rank`.
-- source:
--   supports net0O2_e2_PE_pos

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem net0O2_e2_K_rank (a o c : ℕ) (ha : a < v) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    (K S0 Si0 (Pl a) (Dm o c)).rank = rkC o c := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
