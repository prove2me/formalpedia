-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_sc_stages_run
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_sc_stages_run
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:14:55.978157+00:00
-- url     : https://prove2.me/theorems/321cc033-dbb4-4ec6-b35b-3d7b05463c9c
-- title:
--   Stage-one then stage-two scalar routing on net0O
-- statement:
--   The concatenated stage-one and stage-two scalar circuits of \(\mathtt{net0O}\) route the initial role vector \(v\) so that wire \(\rho(w)\) holds \(v(w)\).

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
theorem net0O2_sc_stages_run
    (v : Fin 104719230 → ZMod 2) (w : Fin 104719230) :
    ((List.range 1771).flatMap (blk2 (toNB ch0O))).foldl scalarStepH
      (((List.range 1771).flatMap (blk1 (toNB ch0O))).foldl scalarStepH
        (Sum.elim v fun _ => 0)) (.inl (net0O.ρ w)) = v w := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
