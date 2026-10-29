-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_entE_width484
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_entE_width484
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:43:40.984989+00:00
-- url     : https://prove2.me/theorems/b9a35d67-0d3b-4fb2-b1c4-be33352b4132
-- title:
--   entE on w < wEnt has head-width 484
-- statement:
--   For every stage-two index $a<v$ and entrance wire $w<w_{\mathrm{Ent}}$, the densified entrance edge $\mathrm{entE}(a,w)$ has one-run head-width exactly $484$:
--   $$
--   w\bigl(\mathrm{entE}(a,w)\bigr)=484.
--   $$
--   This records that $\mathrm{entE}$ selects an $e_n$ child (via $\mathrm{en}$) whose Bruhat run is $[(0,0,484)]$.
--
--   **Formalization Note.** Uses `en_PE` / `pickE` success and `oneRun 484`.
-- source:
--   QHNet entE; OneRun2 en; en_PE

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
theorem net0O2_entE_width484 (a w : ℕ) (ha : a < v) (hw : w < wEnt) :
    (Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2)
      (NB.entE (toNB ch0O) a w).runs.head?).getD 0 = 484 := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
