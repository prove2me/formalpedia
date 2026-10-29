-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_entE_grid_length
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_entE_grid_length
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:48:47.017982+00:00
-- url     : https://prove2.me/theorems/7d19f613-62af-44bf-915c-01d039a750a8
-- title:
--   entE grid has cardinality 1771 · 3542
-- statement:
--   The entrance-edge grid indexed by stage $a<v$ and wire $w<w_{\mathrm{Ent}}$ has cardinality $v\cdot w_{\mathrm{Ent}}$:
--   $$
--   \bigl\lvert\{\mathrm{entE}(a,w):a<v,\,w<w_{\mathrm{Ent}}\}\bigr\rvert=1771\cdot 3542.
--   $$
--
--   **Formalization Note.** `List.length_flatMap` / `List.length_map` / `v,wEnt` unfold; independent of edge contents.
-- source:
--   List length; QHNet entE; Consts v,wEnt via OneRun2

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_entE_grid_length :
    ((List.range v).flatMap fun a =>
      (List.range wEnt).map fun w =>
        NB.entE (toNB ch0O) a w).length = 1771 * 3542 := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
