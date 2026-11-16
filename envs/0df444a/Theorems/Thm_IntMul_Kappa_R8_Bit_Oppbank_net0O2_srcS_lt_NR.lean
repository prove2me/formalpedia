-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_srcS_lt_NR
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_srcS_lt_NR
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:15:42.067201+00:00
-- url     : https://prove2.me/theorems/a49fba81-d15e-497f-afe3-c34e66d52ca0
-- title:
--   Source slots of densified LocSlots lie strictly below NR
-- statement:
--   Every densified LocSlots source index $\mathrm{srcS}(t)$ for $t<v=1771$ is strictly below $NR=27794$.
--
--   Formally,
--   $$
--   \forall\, t < v,\qquad \mathrm{srcS}(t) < NR.
--   $$
--
--   Used by `copyo` wires in $W_{1F}$ ($w_S(\mathrm{srcS}\,t)$).
--
--   Formalization Note. Chunked `List.all`/`decide` over the SRC table (no `native_decide`).
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: LocSlots numeral certificates

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NR v)
theorem net0O2_srcS_lt_NR (t : ℕ) (ht : t < v) : srcS t < NR := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
