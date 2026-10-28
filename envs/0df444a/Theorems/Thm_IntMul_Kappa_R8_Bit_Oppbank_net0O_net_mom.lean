-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O_net_mom
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O_net_mom
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:20:43.473957+00:00
-- url     : https://prove2.me/theorems/ad2b5367-1694-4248-b95b-036f685354e1
-- title:
--   EM-sum of net0O equals histMoment oppbankHist
-- statement:
--   For every $\tau\in\mathbb{R}$, the edge-moment sum of the one-run opp-bank network equals the target histogram moment:
--
--   $$\sum_{e\in\mathrm{net0O}.\mathrm{edges}}\mathrm{EM}_\tau(e)=\mathrm{histMoment}(\mathrm{oppbankHist},529,\tau).$$
--
--   With OneRunMom `hist_mom_net0O` this yields `net0O_hist_eq_oppbank`.
-- source:
--   OneRunMom EM_oneRun; GenCN/SideRanks; oppbankHist; R6 net_mom pattern

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom

theorem net0O_net_mom (τ : ℝ) :
    (net0O.edges.map (EM τ)).sum = histMoment oppbankHist 529 τ := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
