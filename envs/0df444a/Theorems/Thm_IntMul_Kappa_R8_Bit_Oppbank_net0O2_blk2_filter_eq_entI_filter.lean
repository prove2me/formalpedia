-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk2_filter_eq_entI_filter
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_blk2_filter_eq_entI_filter
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:38:45.676344+00:00
-- url     : https://prove2.me/theorems/5f3b85ef-adc2-4860-ade2-542f53adefb8
-- title:
--   blk2 width-484 filter equals entI width-484 filter
-- statement:
--   Because each stage-two tail contributes no head-width $484$, filtering stage-two edges by width $484$ retains exactly the entrance edges:
--   $$
--   \mathrm{filter}_{w=484}(\mathrm{progEdges}(\mathrm{blk2}))=\mathrm{filter}_{w=484}(\mathrm{progEdges}(\mathrm{entI})).
--   $$
--
--   **Formalization Note.** Uses per-block blk2 = entI ++ tail and empty tail filters.
-- source:
--   OneRun2 blk2

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_blk2_filter_eq_entI_filter :
    (List.filter
      (fun e : Edge 529 =>
        decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))
      (((List.range v).flatMap (NB.blk2 (toNB ch0O))).filterMap Instr.edgeOf)) =
    (List.filter
      (fun e : Edge 529 =>
        decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))
      (((List.range v).flatMap (NB.entI (toNB ch0O))).filterMap Instr.edgeOf)) := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
