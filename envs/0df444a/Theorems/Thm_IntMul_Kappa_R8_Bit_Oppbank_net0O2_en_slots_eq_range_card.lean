-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_en_slots_eq_range_card
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_en_slots_eq_range_card
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:39:07.256985+00:00
-- url     : https://prove2.me/theorems/bd423eb6-beec-463f-a80f-597c8c61a71e
-- title:
--   Width-484 edge count equals range v × wEnt cardinality
-- statement:
--   The densified data-entrance edges of $\mathrm{net0O}$ (one-run head-width $484$) are in bijection with the combinatorial entrance index set $[0,v)\times[0,w_{\mathrm{Ent}})$, so their counts agree:
--   $$
--   \#\{e:\,w(e)=484\}=\lvert[0,1771)\times[0,3542)\rvert.
--   $$
--
--   **Formalization Note.** Bridges `net0O2_en_slots_count` to `net0O2_range_v_wEnt_card`.
-- source:
--   OneRun2 entI; en_slots; range_v_wEnt_card

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
theorem net0O2_en_slots_eq_range_card :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))).length =
      ((List.range 1771).flatMap fun _ => List.range 3542).length := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
