-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ec_K_rank
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_ec_K_rank
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:13:40.611124+00:00
-- url     : https://prove2.me/theorems/8caa09b9-d797-453c-abef-5baad6c38f91
-- title:
--   Rank of ec residual is 1
-- statement:
--   $\mathrm{rank}\,K(S_0,S_i,\mathrm{Pl}(a),\mathrm{Pl}(s))=1$ (product of rank-$1$ projectors under conjugation).
--
--   **Formalization Note.** Hypothesis for `oneRun1_of_piv`.
-- source:
--   supports net0O2_ec_PE via OneRunPE2.oneRun1_of_piv

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem net0O2_ec_K_rank (a s : ℕ) (ha : a < v) (hs : s < v) :
    (K S0 Si0 (Pl a) (Pl s)).rank = 1 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
