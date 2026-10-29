-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_entI_filter_eq_entE_grid
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_entI_filter_eq_entE_grid
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:23:39.923994+00:00
-- url     : https://prove2.me/theorems/4f31edf4-86d1-475d-9454-734012577975
-- title:
--   entI width-484 filter equals the entE grid
-- statement:
--   Among entrance instructions $\mathrm{entI}$, the edges of head-width $484$ are exactly the densified entrance grid: for each $a<v$ the wires $w<w_{\mathrm{Ent}}$ contribute $\mathrm{entE}(a,w)$ of width $484$, while wires $w_{\mathrm{Ent}}\le w<w_{\mathrm{AuxEnd}}$ contribute exits $e_i$ of width $22$.
--   $$
--   \mathrm{filter}_{w=484}(\mathrm{progEdges}(\mathrm{entI}))=\{\mathrm{entE}(a,w):a<v,\,w<w_{\mathrm{Ent}}\}.
--   $$
--
--   **Formalization Note.** List equality after `filterMap Instr.edgeOf` on flatMapped `entI`.
-- source:
--   OneRun2 entI/entE; mom width484_edges_from_entI

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_entI_filter_eq_entE_grid :
    ((List.range v).flatMap fun a =>
        (NB.entI (toNB ch0O) a).filterMap Instr.edgeOf).filter
      (fun e : Edge 529 =>
        decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484)) =
      ((List.range v).flatMap fun a =>
        (List.range wEnt).map fun w => NB.entE (toNB ch0O) a w) := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
