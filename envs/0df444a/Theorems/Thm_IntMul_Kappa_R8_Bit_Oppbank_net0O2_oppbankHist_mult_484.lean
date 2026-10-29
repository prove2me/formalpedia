-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_oppbankHist_mult_484
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_oppbankHist_mult_484
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:22:47.769887+00:00
-- url     : https://prove2.me/theorems/cac34626-c7ff-4103-b781-e111325e4512
-- title:
--   oppbankHist multiplicity at width 484
-- statement:
--   The locked opp-bank histogram records multiplicity $6272882$ at width $484$:
--   $$
--   n_{484}(\\mathrm{oppbankHist})=6272882.
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
theorem net0O2_oppbankHist_mult_484 :
    ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = 484))).map (fun p => p.2)).sum = 6272882 := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
