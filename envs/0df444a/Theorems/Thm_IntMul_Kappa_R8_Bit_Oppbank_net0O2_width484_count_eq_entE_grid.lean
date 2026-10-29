-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_width484_count_eq_entE_grid
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_width484_count_eq_entE_grid
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:06:23.4671+00:00
-- url     : https://prove2.me/theorems/b7c78223-de1c-4b81-bc30-d6d9a2ff55a9
-- title:
--   Width-484 edge count equals entE grid length
-- statement:
--   The number of $\mathrm{net0O}$ edges of one-run head-width $484$ equals the cardinality of the densified entrance grid:
--   $$
--   \#\{e:\,w(e)=484\}=\lvert\{\mathrm{entE}(a,w):a<v,\,w<w_{\mathrm{Ent}}\}\rvert.
--   $$
--   Every such edge arises from an $\mathrm{entI}$ entrance slot, and every entrance slot contributes width $484$.
--
--   **Formalization Note.** Length form of `width484_edges_from_entI` (avoids list-order identification).
-- source:
--   OneRun2 entI; en_slots; entE_grid_length

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_width484_count_eq_entE_grid :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))).length =
      ((List.range v).flatMap fun a =>
        (List.range wEnt).map fun w =>
          NB.entE (toNB ch0O) a w).length := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
