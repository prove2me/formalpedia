-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk2_after_entI_width_ne_484
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_blk2_after_entI_width_ne_484
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:38:53.033429+00:00
-- url     : https://prove2.me/theorems/0496f738-c704-4167-859d-2c901b8c5458
-- title:
--   blk2 edges after entI never have head-width 484
-- statement:
--   After the entrance segment of each stage-two block, remaining edges are chunk edges $e_2$ (widths $\mathrm{rkC}$) and correction edges $e_c$ (width $1$). Neither family has head-width $484$.
--   $$
--   \mathrm{filter}_{w=484}(\mathrm{progEdges}(e_2+\mathrm{corrI}))=\emptyset.
--   $$
--
--   **Formalization Note.** FlatMap over $a<v$ of chunkProg e2 ++ corrI; List.filter without pipe syntax.
-- source:
--   OneRun2 blk2 tail

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_blk2_after_entI_width_ne_484 :
    (List.filter
      (fun e : Edge 529 =>
        decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))
      (((List.range v).flatMap fun a =>
          NB.chunkProg (NB.ι2 a) ((toNB ch0O).e2 a) NB.cs2 ++
            (List.range v).flatMap (NB.corrI (toNB ch0O) a)).filterMap Instr.edgeOf)) = [] := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
