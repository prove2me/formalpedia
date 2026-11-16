-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_injS_lt_NR_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_injS_lt_NR_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:47:15.313789+00:00
-- url     : https://prove2.me/theorems/4457d5af-2288-4e3f-9a28-774906cdca62
-- title:
--   Injection slots of densified LocSlots lie strictly below NR (QHNetRec)
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
--
--   This is the same slot-bound certificate as `net0O2_injS_lt_NR`, restated against the total-decoder fork `IntMul_Kappa_R8_Data_BitOppbankQHNetRec` (the accessors `retS`, `srcS`, `injS`, and `pts` are unchanged; only the GREC decoder is total). It does not import the parent module `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: LocSlots numeral certificates Restated on QHNetRec (Nat.rec chunkDec fork d127abea) as IntMul.Kappa.R8.Bit.Oppbank.net0O2_injS_lt_NR_rec; does not close the parent theorem.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NR v)
theorem net0O2_injS_lt_NR_rec (T k : ℕ) (hT : T < v) (hk : k < 3) : injS T k < NR := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
