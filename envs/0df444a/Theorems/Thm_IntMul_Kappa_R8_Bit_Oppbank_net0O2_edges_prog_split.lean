-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_edges_prog_split
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_edges_prog_split
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:23:59.697038+00:00
-- url     : https://prove2.me/theorems/b93b72cb-0db4-45ed-a2cf-ec1e7e84d419
-- title:
--   net0O.edges splits into blk1 / entI / blk2-tail
-- statement:
--   The edge list of $\mathrm{net0O}$ is the concatenation of three program segments: stage-one blocks, entrance instructions $\mathrm{entI}$, and the stage-two tail (chunk edges $e_2$ with correction edges $e_c$).
--   $$
--   \mathrm{edges}(\mathrm{net0O})=\mathrm{progEdges}(\mathrm{blk1})\;+\!\!+\;\mathrm{progEdges}(\mathrm{entI})\;+\!\!+\;\mathrm{progEdges}(e_2+\mathrm{corr}).
--   $$
--   This is the structural splitting used to locate width-$484$ edges inside $\mathrm{entI}$.
--
--   **Formalization Note.** Unfolds `QHNet.edges` / `prog` / `blk2` and uses `List.filterMap_append`.
-- source:
--   OneRun2 prog structure; mom width484_edges_from_entI

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_edges_prog_split :
    net0O.edges =
      ((List.range v).flatMap (NB.blk1 (toNB ch0O))).filterMap Instr.edgeOf ++
        ((List.range v).flatMap fun a => (NB.entI (toNB ch0O) a)).filterMap Instr.edgeOf ++
          ((List.range v).flatMap fun a =>
              NB.chunkProg (NB.ι2 a) ((toNB ch0O).e2 a) NB.cs2 ++
                (List.range v).flatMap (NB.corrI (toNB ch0O) a)).filterMap Instr.edgeOf := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
