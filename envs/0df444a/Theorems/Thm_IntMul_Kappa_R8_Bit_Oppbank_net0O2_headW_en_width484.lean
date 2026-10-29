-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_headW_en_width484
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_headW_en_width484
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:44:34.499832+00:00
-- url     : https://prove2.me/theorems/97133c2c-3fc1-4303-a4c7-03e24f731cea
-- title:
--   en-family edges realize oppbankHist width-484 multiplicity
-- statement:
--   The $e_n$ family (one-run width $484$) accounts for $n_{484}(\mathrm{oppbankHist})$.
--   $$
--   \#\{e:\,w(e)=484\}=n_{484}(\mathrm{oppbankHist}).
--   $$
--
--   **Formalization Note.** Instance of `headW_fixed_widths` at $w=484$.
-- source:
--   OneRun2 ch0O; Hist; headW_fixed_widths cb324006

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
theorem net0O2_headW_en_width484 :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 484))).length =
      ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = 484))).map (fun p => p.2)).sum := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
