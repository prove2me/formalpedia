-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_oneRunV_oppbank
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_oneRunV_oppbank
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:02:48.602986+00:00
-- url     : https://prove2.me/theorems/09d96d88-2ba7-4ab5-b008-c18c225ba0c3
-- title:
--   oneRunV sum over net0O edges equals histMoment oppbankHist
-- statement:
--   The multiset of one-run widths on `net0O` matches the locked opposite-bank histogram `oppbankHist`, hence
--   $$\sum_e \mathrm{oneRunV}_\tau(w(e))=\mathrm{histMoment}(\mathrm{oppbankHist},529,\tau).$$
--   Fed by GenCN/SideRanks rank counts versus Jain `bit_hist.onerun_hist`.
--
--   **Formalization Note.** Companion leaf to `net0O2_EM_sum_oneRunV` for `net0O2_net_mom`.
-- source:
--   OneRun2; Hist cb4b257b; GenCN/SideRanks

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2

theorem net0O2_oneRunV_oppbank (τ : ℝ) :
    (net0O.edges.map fun e => oneRunV τ (e.runs.head?.map (·.2.2) |>.getD 0)).sum =
      histMoment oppbankHist 529 τ := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
