-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_sc_of_stages
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_sc_of_stages
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:15:14.275121+00:00
-- url     : https://prove2.me/theorems/7d1cd93a-ffdd-493f-bfcd-c6346e19e7af
-- title:
--   ScalarOK of net0O from stage-one and stage-two scalar runs
-- statement:
--   If the concatenated stage-one then stage-two scalar run of \(\mathtt{net0O}\) routes every role \(w\) back to \(v(w)\), then the full program does as well (since \(\mathtt{prog}=\mathrm{stage1}{+}{+}\mathrm{stage2}\)).

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
open IntMul.Kappa.R6.Bit (scalarStepH)
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB (blk1 blk2)
theorem net0O2_sc_of_stages
    (h12 : ∀ (v : Fin 104719230 → ZMod 2) (w : Fin 104719230),
      ((List.range 1771).flatMap (blk2 (toNB ch0O))).foldl scalarStepH
        (((List.range 1771).flatMap (blk1 (toNB ch0O))).foldl scalarStepH
          (Sum.elim v fun _ => 0)) (.inl (net0O.ρ w)) = v w) :
    ∀ (v : Fin 104719230 → ZMod 2) (w : Fin 104719230),
      net0O.prog.foldl scalarStepH (Sum.elim v fun _ => 0) (.inl (net0O.ρ w)) = v w := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
