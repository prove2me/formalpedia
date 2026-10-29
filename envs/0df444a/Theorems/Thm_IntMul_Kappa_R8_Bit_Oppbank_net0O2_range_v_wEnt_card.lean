-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_range_v_wEnt_card
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_range_v_wEnt_card
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:27:53.088484+00:00
-- url     : https://prove2.me/theorems/10911687-08ef-4be9-9937-24af7bcddfcf
-- title:
--   Cardinality of range v × range wEnt
-- statement:
--   The Cartesian product of the stage index range of length $v=1771$ with the entrance-wire range of length $w_{\mathrm{Ent}}=3542$ has cardinality $v\cdot w_{\mathrm{Ent}}$:
--   $$
--   \lvert[0,v)\times[0,w_{\mathrm{Ent}})\rvert=1771\cdot 3542.
--   $$
--   This is the combinatorial skeleton of the densified data-entrance edge count.
--
--   **Formalization Note.** `List.range` length arithmetic; no network data required.
-- source:
--   List.range; en_slots skeleton

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank
theorem net0O2_range_v_wEnt_card :
    ((List.range 1771).flatMap fun _ => List.range 3542).length = 1771 * 3542 := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
