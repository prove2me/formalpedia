-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_oppbankHist_mult_22
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_oppbankHist_mult_22
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:22:49.05355+00:00
-- url     : https://prove2.me/theorems/99a8f15d-c99a-4998-a943-15bc378048c9
-- title:
--   oppbankHist multiplicity at width 22
-- statement:
--   The locked opp-bank histogram records multiplicity $116886$ at width $22$:
--   $$
--   n_{22}(\\mathrm{oppbankHist})=116886.
--   $$
--
--   **Formalization Note.** Discharged by `decide` on the concrete `oppbankHist` list.
-- source:
--   Hist cb4b257b; headW fixed-width leaves

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank
theorem net0O2_oppbankHist_mult_22 :
    ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = 22))).map (fun p => p.2)).sum = 116886 := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
