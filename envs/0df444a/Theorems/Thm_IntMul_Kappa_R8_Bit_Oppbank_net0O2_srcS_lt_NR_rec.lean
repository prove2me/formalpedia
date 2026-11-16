-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_srcS_lt_NR_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_srcS_lt_NR_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:46:43.944208+00:00
-- url     : https://prove2.me/theorems/cba676ad-be21-4265-8a0a-5edc4f5a8109
-- title:
--   Source slots of densified LocSlots lie strictly below NR (QHNetRec)
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
--
--   This is the same slot-bound certificate as `net0O2_srcS_lt_NR`, restated against the total-decoder fork `IntMul_Kappa_R8_Data_BitOppbankQHNetRec` (the accessors `retS`, `srcS`, `injS`, and `pts` are unchanged; only the GREC decoder is total). It does not import the parent module `Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: LocSlots numeral certificates Restated on QHNetRec (Nat.rec chunkDec fork d127abea) as IntMul.Kappa.R8.Bit.Oppbank.net0O2_srcS_lt_NR_rec; does not close the parent theorem.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NR v)
theorem net0O2_srcS_lt_NR_rec (t : ℕ) (ht : t < v) : srcS t < NR := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
