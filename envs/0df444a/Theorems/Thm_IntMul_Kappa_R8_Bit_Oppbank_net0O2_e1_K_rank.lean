-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e1_K_rank
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_e1_K_rank
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:07:30.679655+00:00
-- url     : https://prove2.me/theorems/e68e4320-7ab2-4a14-a40b-e2581cd5d851
-- title:
--   Rank of e1 residual equals $\mathrm{rkC}$
-- statement:
--   # Rank of the stage-one densified residual
--
--   Under the same in-range / positive-rank hypotheses,
--   $$
--   \mathrm{rank}\,K(S_0,S_i,\mathrm{Dm}(o,c),\mathrm{Pl}(b)) = \mathrm{rkC}(o,c).
--   $$
--   Together with idempotence this feeds `oneRun_of_pivs`.
--
--   **Formalization Note.** Uses $\mathrm{rank}(\mathrm{Dm})=\mathrm{rkC}$, $\mathrm{rank}(\mathrm{Pl})=1$, and conjugation by invertible $S_0$.
-- source:
--   BitNB OneRun2 mom-path 2026-10-29; supports net0O2_e1_PE_pos / AllOneRun

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open Matrix

theorem net0O2_e1_K_rank (b o c : ℕ) (hb : b < v) (ho : o < codeBound) (hc : c < codeBound)
    (hr : 0 < rkC o c) :
    (K S0 Si0 (Dm o c) (Pl b)).rank = rkC o c := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
