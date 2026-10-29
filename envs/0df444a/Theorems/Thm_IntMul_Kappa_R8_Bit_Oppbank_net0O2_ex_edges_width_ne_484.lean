-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_ex_edges_width_ne_484
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_ex_edges_width_ne_484
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:38:59.345842+00:00
-- url     : https://prove2.me/theorems/f2117a84-df5a-474a-917a-f84a6559a5e6
-- title:
--   Stage-one exit edges never have head-width 484
-- statement:
--   Auxiliary exit edges $e_x$ have one-run head-width $22$, so none survive a width-$484$ filter.
--   $$
--   \mathrm{filter}_{w=484}(\mathrm{progEdges}(\mathrm{ex}))=\emptyset.
--   $$
--
--   **Formalization Note.** List.filter on filterMap of flatMapped exit Instr.edge list.
-- source:
--   OneRun2 ex widths

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_ex_edges_width_ne_484 :
    (List.filter
      (fun e : Edge 529 =>
        decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))
      ((List.range v).flatMap fun b =>
        (List.range' wEnt NR).map fun _ => (toNB ch0O).ex b)) = [] := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
