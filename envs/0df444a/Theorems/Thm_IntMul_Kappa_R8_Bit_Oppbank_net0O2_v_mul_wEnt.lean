-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_v_mul_wEnt
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_v_mul_wEnt
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:06:26.355723+00:00
-- url     : https://prove2.me/theorems/ce7bb507-46cf-4ca1-b315-9f7042b39b61
-- title:
--   $v\cdot w_{\mathrm{Ent}}=6272882$
-- statement:
--   Geometry identity for the densified opp-bank layout:
--   $$
--   v\cdot w_{\mathrm{Ent}}=1771\cdot 3542=6272882=2N.
--   $$
--   Equals the locked $n_{484}$ of $\mathrm{oppbankHist}$ / Jain one-run data-entrance count.
--
--   **Formalization Note.** Discharged by `decide`.
-- source:
--   BitOppbankConsts v,wEnt,N; Hist n_484

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankConsts
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R8.Bit.Oppbank

theorem net0O2_v_mul_wEnt : v * wEnt = 6272882 := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
