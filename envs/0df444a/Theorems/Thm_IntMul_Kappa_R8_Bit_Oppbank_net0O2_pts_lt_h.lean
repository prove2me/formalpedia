-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_pts_lt_h
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_pts_lt_h
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:15:43.642524+00:00
-- url     : https://prove2.me/theorems/e9c73f3b-bac5-4025-a126-a53fa28d77da
-- title:
--   pts of densified LocSlots lie strictly below h
-- statement:
--   Every densified LocSlots point index $\mathrm{pts}(T,k)$ for $T<v=1771$ and $k<3$ is strictly below $h=23$.
--
--   Formally,
--   $$
--   \forall\, T < v,\ \forall\, k < 3,\qquad \mathrm{pts}(T,k) < h.
--   $$
--
--   Used by `scat`/`rdS` wires in $W_{1F}$ (via $w_T$).
--
--   Formalization Note. Chunked `decide` over the TPTS table (no `native_decide`).
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
open IntMul.Kappa.R8.Bit.Oppbank (h v)
theorem net0O2_pts_lt_h (T k : ℕ) (hT : T < v) (hk : k < 3) : pts T k < h := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
