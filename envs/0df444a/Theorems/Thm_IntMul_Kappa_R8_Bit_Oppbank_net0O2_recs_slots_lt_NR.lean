-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_recs_slots_lt_NR
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_recs_slots_lt_NR
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:15:55.989661+00:00
-- url     : https://prove2.me/theorems/9e5a2ee4-6827-42a6-807c-e51ee61ecfdb
-- title:
--   GREC recs pivot, exit, and operand slots lie strictly below NR
-- statement:
--   Every densified GREC record in the LocSlots table $\mathrm{recs}$ has all of its pivot, exit, and operand indices strictly below $NR=27794$.
--
--   A record $r\in\mathrm{recs}$ carries a pivot index, an exit field, and a list of operand indices. The exit field is either $0$ (no predecessor) or one more than a slot index. Formally,
--   $$
--   \forall\, r\in\mathrm{recs},\qquad
--   \mathrm{piv}(r)<NR
--   \ \wedge\ \bigl(\mathrm{ex}(r)=0\ \lor\ \mathrm{ex}(r)-1<NR\bigr)
--   \ \wedge\ \bigl(\forall\, o\in\mathrm{ops}(r),\ o<NR\bigr).
--   $$
--
--   This certificate is used by the $W_{1F}$ wire bound when rec-instruction endpoints are sent through the slot map $w_S$.
--
--   **Formalization Note.** `recs` is the flattening of the densified GREC chunks (`GREC.flatMap chunkDec`) in `Oppbank.NB`, with `Rec := ℕ × ℕ × ℕ × List ℕ`. The statement is written with the corresponding product projections.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: LocSlots GREC recs slot certificates (QHNet NB.recs, NR=27794)

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NR)
theorem net0O2_recs_slots_lt_NR :
    ∀ r ∈ recs, r.2.1 < NR ∧ (r.2.2.1 = 0 ∨ r.2.2.1 - 1 < NR) ∧ ∀ o ∈ r.2.2.2, o < NR := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
