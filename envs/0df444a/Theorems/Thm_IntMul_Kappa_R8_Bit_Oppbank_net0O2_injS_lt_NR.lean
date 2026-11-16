-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_injS_lt_NR
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_injS_lt_NR
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:15:43.80949+00:00
-- url     : https://prove2.me/theorems/5bb13388-0253-4ac7-842f-d3ebe776312f
-- title:
--   Injection slots of densified LocSlots lie strictly below NR
-- statement:
--   Every densified LocSlots injection index $\mathrm{injS}(T,k)$ for $T<v=1771$ and $k<3$ is strictly below $NR=27794$.
--
--   Formally,
--   $$
--   \forall\, T < v,\ \forall\, k < 3,\qquad \mathrm{injS}(T,k) < NR.
--   $$
--
--   Used by `injo` wires in $W_{1F}$.
--
--   Formalization Note. Chunked `decide` over the INJ table (no `native_decide`).
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
theorem net0O2_injS_lt_NR (T k : ℕ) (hT : T < v) (hk : k < 3) : injS T k < NR := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
