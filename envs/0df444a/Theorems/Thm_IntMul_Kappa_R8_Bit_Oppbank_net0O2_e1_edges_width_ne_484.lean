-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_e1_edges_width_ne_484
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_e1_edges_width_ne_484
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:38:46.081531+00:00
-- url     : https://prove2.me/theorems/ad76f820-2615-4847-a432-cc83200fe6a7
-- title:
--   Stage-one chunk edges never have head-width 484
-- statement:
--   Chunk edges arising from stage-one $e_1$ families have one-run head-width equal to a cell rank $\mathrm{rkC}$, never $484$.
--   $$
--   \mathrm{filter}_{w=484}(\mathrm{progEdges}(e_1))=\emptyset.
--   $$
--
--   **Formalization Note.** List.filter on filterMap of flatMapped chunkProg e1.
-- source:
--   OneRun2 e1 widths

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_e1_edges_width_ne_484 :
    (List.filter
      (fun e : Edge 529 =>
        decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))
      (((List.range v).flatMap fun b =>
          NB.chunkProg (NB.ι1 b) ((toNB ch0O).e1 b) NB.cs1).filterMap Instr.edgeOf)) = [] := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
