-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_headW_ex_ei_width22
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_headW_ex_ei_width22
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:44:35.520026+00:00
-- url     : https://prove2.me/theorems/917c5764-0fea-4dc1-a045-c64ab5787993
-- title:
--   ex/ei-family edges realize oppbankHist width-22 multiplicity
-- statement:
--   The $e_x$ and $e_i$ families (one-run width $22$) jointly account for $n_{22}(\mathrm{oppbankHist})$.
--   $$
--   \#\{e:\,w(e)=22\}=n_{22}(\mathrm{oppbankHist}).
--   $$
--
--   **Formalization Note.** Instance of `headW_fixed_widths` at $w=22$.
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
theorem net0O2_headW_ex_ei_width22 :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 22))).length =
      ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = 22))).map (fun p => p.2)).sum := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
