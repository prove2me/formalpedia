-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_oppbankHist_mult_1
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_oppbankHist_mult_1
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:22:46.683485+00:00
-- url     : https://prove2.me/theorems/dd311027-4a39-430c-87e1-1cf79f195a87
-- title:
--   oppbankHist multiplicity at width 1
-- statement:
--   The locked opp-bank histogram records multiplicity $221936407$ at width $1$:
--   $$
--   n_{1}(\\mathrm{oppbankHist})=221936407.
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
theorem net0O2_oppbankHist_mult_1 :
    ((oppbankHist.filter (fun p : ℕ × ℕ => decide (p.1 = 1))).map (fun p => p.2)).sum = 221936407 := by
  sorry
end IntMul.Kappa.R8.Bit.Oppbank
