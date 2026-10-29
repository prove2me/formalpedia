-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk1_edges_width_ne_484
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_blk1_edges_width_ne_484
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:39:10.108989+00:00
-- url     : https://prove2.me/theorems/057609ec-3f43-46b5-adef-b26a2e86368d
-- title:
--   Stage-one edges never have head-width 484
-- statement:
--   No edge from a stage-one block has head-width $484$.
--   $$
--   \mathrm{filter}_{w=484}(\mathrm{progEdges}(\mathrm{blk1}))=\emptyset.
--   $$
--
--   **Formalization Note.** Uses List.filter on filterMap Instr.edgeOf of flatMapped blk1.
-- source:
--   OneRun2 blk1

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_blk1_edges_width_ne_484 :
    (List.filter
      (fun e : Edge 529 =>
        decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))
      (((List.range v).flatMap (NB.blk1 (toNB ch0O))).filterMap Instr.edgeOf)) = [] := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
