-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_net_mom
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_net_mom
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:38:40.247995+00:00
-- url     : https://prove2.me/theorems/5cdd4073-adcf-4643-8011-b69711c2cdd7
-- title:
--   EM-sum of OneRun2 net0O equals histMoment oppbankHist
-- statement:
--   For every $\tau\in\mathbb{R}$, the edge-moment sum of the corrected one-run opp-bank network equals the target histogram moment:
--
--   $$\sum_{e\in\mathrm{net0O}.\mathrm{edges}}\mathrm{EM}_\tau(e)=\mathrm{histMoment}(\mathrm{oppbankHist},529,\tau).$$
--
--   With OneRunMom2 `hist_mom_net0O` this yields `net0O2_hist_eq_oppbank`. Requires PE inhabitance (OneRunPE2) so channel edges are real one-run edges rather than `dfltE`.
--
--   **Formalization Note.** Carrier `OneRunNet2.net0O`.
-- source:
--   OneRun2 e0d447f6; OneRunMom2 a4deb37c; Hist cb4b257b

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

theorem net0O2_net_mom (τ : ℝ) :
    (net0O.edges.map (EM τ)).sum = histMoment oppbankHist 529 τ := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
