-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk1_edges_from_e1_ex
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_blk1_edges_from_e1_ex
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:38:47.15452+00:00
-- url     : https://prove2.me/theorems/d7f2ae21-744a-4af9-a88a-2e76c7041478
-- title:
--   Stage-one edges split into e1-chunk and ex families
-- statement:
--   Each stage-one block is the concatenation of an $e_1$-chunk program and aux-exit instructions, so the extracted edge list splits as
--   $$
--   \mathrm{progEdges}(\mathrm{blk1})=\mathrm{progEdges}(e_1)\mathbin{+\!+}\mathrm{progEdges}(\mathrm{ex}).
--   $$
--
--   **Formalization Note.** Unfolds NB.blk1 and applies filterMap_append after flatMap-append.
-- source:
--   OneRun2 blk1 split

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_blk1_edges_from_e1_ex :
    ((List.range v).flatMap (NB.blk1 (toNB ch0O))).filterMap Instr.edgeOf =
      ((List.range v).flatMap fun b =>
          NB.chunkProg (NB.ι1 b) ((toNB ch0O).e1 b) NB.cs1).filterMap Instr.edgeOf ++
        ((List.range v).flatMap fun b =>
          (List.range' wEnt NR).map fun _ => (toNB ch0O).ex b) := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
