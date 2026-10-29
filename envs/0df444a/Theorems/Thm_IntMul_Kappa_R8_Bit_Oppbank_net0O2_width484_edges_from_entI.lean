-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_width484_edges_from_entI
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_width484_edges_from_entI
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:43:39.941535+00:00
-- url     : https://prove2.me/theorems/c76868ac-a649-4be6-bb25-788dc9ac58a1
-- title:
--   Width-484 edges arise exactly from entI entrance slots
-- statement:
--   Every $\mathrm{net0O}$ edge of one-run head-width $484$ is exactly an entrance edge produced by $\mathrm{entI}$ on stage-two blocks: for each $a<v$ and each local wire $w<w_{\mathrm{Ent}}$, the instruction uses $\mathrm{entE}$ (hence an $e_n$ child of width $484$). No other program family contributes width $484$.
--   $$
--   \{e:\,w(e)=484\}=\{\mathrm{entE}(a,w):a<v,\,w<w_{\mathrm{Ent}}\}.
--   $$
--
--   **Formalization Note.** List equality of the filtered edge list with the entI-produced edges (as lists, order from `prog`).
-- source:
--   QHNet entI/entE; OneRun2 en oneRun 484; bit_hist data entrance

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_width484_edges_from_entI :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))) =
      ((List.range v).flatMap fun a =>
        (List.range wEnt).map fun w =>
          NB.entE (toNB ch0O) a w) := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
