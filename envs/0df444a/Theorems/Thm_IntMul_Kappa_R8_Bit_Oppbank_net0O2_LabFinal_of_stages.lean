-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_LabFinal_of_stages
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_LabFinal_of_stages
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:53:48.88797+00:00
-- url     : https://prove2.me/theorems/eadf7d1d-91f9-41dc-a0a6-2f7e6fcd5482
-- title:
--   LabFinal of net0O from stage label runs
-- statement:
--   If after concatenating stage-one then stage-two of \(\mathtt{net0O}\) every role wire \(\rho(w)\) carries label \(\mathrm{swapMat}\), then the same holds for the full program fold (since \(\mathtt{prog}=\mathrm{stage1}{+}{+}\mathrm{stage2}\)).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace IntMul.Kappa.R8.Bit.Oppbank
open AModel (swapMat)
open IntMul.Kappa.R6.Bit (labStepH)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB (blk1 blk2)
theorem net0O2_LabFinal_of_stages (N : ℕ) (h : EOKO ch0NB N)
    (h2 : ∀ w, ((List.range 1771).flatMap (blk2 (toNB ch0O))).foldl (labStepH N)
      (((List.range 1771).flatMap (blk1 (toNB ch0O))).foldl (labStepH N) (fun _ => 1))
      (.inl (net0O.ρ w)) = swapMat) :
    ∀ w, net0O.prog.foldl (labStepH N) (fun _ => 1) (.inl (net0O.ρ w)) = swapMat := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
