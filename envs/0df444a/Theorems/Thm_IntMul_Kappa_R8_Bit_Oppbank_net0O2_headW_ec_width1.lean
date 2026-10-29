-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_headW_ec_width1
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_headW_ec_width1
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:44:44.754341+00:00
-- url     : https://prove2.me/theorems/863e4332-acee-4962-8c08-4179abe1d0a7
-- title:
--   ec-family edges realize oppbankHist width-1 multiplicity
-- statement:
--   The $e_c$ family of $\mathrm{net0O}$ (one-run width $1$) accounts for the histogram multiplicity $n_1(\mathrm{oppbankHist})$ after discarding default slots.
--   $$
--   \#\{e:\,w(e)=1\}=n_1(\mathrm{oppbankHist}).
--   $$
--
--   **Formalization Note.** Instance of `headW_fixed_widths` at $w=1$.
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
theorem net0O2_headW_ec_width1 :
    (net0O.edges.filter
        (fun e : Edge 529 =>
          decide ((Option.map (fun ρ : ℕ × ℕ × ℕ => ρ.2.2) e.runs.head?).getD 0 = 1))).length =
      ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = 1))).map (fun p => p.2)).sum := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
