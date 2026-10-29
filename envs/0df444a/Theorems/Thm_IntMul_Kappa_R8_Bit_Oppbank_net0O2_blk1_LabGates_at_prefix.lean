-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk1_LabGates_at_prefix
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_blk1_LabGates_at_prefix
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:07:25.760455+00:00
-- url     : https://prove2.me/theorems/302cdbf6-4ee4-4bfa-94eb-e90455d1d31e
-- title:
--   blk1 LabGates from the stage-one prefix labeling
-- statement:
--   Under \(\mathrm{EOKO}\), the \(i\)-th stage-one block is label-gate consistent from the labeling produced by the preceding stage-one banks \(0..i-1\) starting at constant label \(1\).

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
open IntMul.Kappa.R6.Bit (LabGates labStepH)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB (blk1)
theorem net0O2_blk1_LabGates_at_prefix (N : ℕ) (h : EOKO ch0NB N)
    (i : ℕ) (hi : i < 1771) :
    LabGates N (blk1 (toNB ch0O) i)
      (((List.range i).flatMap (blk1 (toNB ch0O))).foldl (labStepH N) (fun _ => 1)) := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
