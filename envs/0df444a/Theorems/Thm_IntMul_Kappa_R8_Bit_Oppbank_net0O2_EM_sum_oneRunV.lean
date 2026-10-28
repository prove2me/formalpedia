-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_EM_sum_oneRunV
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_EM_sum_oneRunV
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:01:33.030995+00:00
-- url     : https://prove2.me/theorems/480344d9-853e-476f-89e5-7f5cbdbc6bbb
-- title:
--   OneRun2 EM sum equals oneRunV of head widths
-- statement:
--   For the corrected one-run network, every edge realises a true `oneRun` residual (PE inhabited via OneRunPE2), so
--   $$\sum_e \mathrm{EM}_\tau(e)=\sum_e \mathrm{oneRunV}_\tau(w(e)),$$
--   where $w(e)$ is the width of the unique Bruhat run of $e$.
--
--   **Formalization Note.** Uses `Option.getD` on `e.runs.head?` for the empty/`dfltE` case.
-- source:
--   OneRun2 e0d447f6; OneRunMom2 a4deb37c; OneRunPE2 b8f301c1

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRunMom2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntMul.Kappa.R8.Bit.Oppbank

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunMom2

theorem net0O2_EM_sum_oneRunV (τ : ℝ) :
    (net0O.edges.map (EM τ)).sum =
      (net0O.edges.map fun e => oneRunV τ (e.runs.head?.map (·.2.2) |>.getD 0)).sum := by
  sorry

end IntMul.Kappa.R8.Bit.Oppbank
