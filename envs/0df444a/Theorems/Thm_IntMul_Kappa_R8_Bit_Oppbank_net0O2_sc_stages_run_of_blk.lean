-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_sc_stages_run_of_blk
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_sc_stages_run_of_blk
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:25:16.423455+00:00
-- url     : https://prove2.me/theorems/86520843-53df-4f7d-9eb7-82ac8bdbff76
-- title:
--   Staged scalar routing from per-bank scalar facts
-- statement:
--   Glue leaf: staged scalar routing of \(\mathtt{net0O}\) follows from per-bank stage-one/stage-two scalar identities (to be filled).

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
theorem net0O2_sc_stages_run_of_blk
    (h1 : ∀ (vec : Fin 104719230 ⊕ Fin 3217907 → ZMod 2) (b : ℕ), b < 1771 → True)
    (h2 : ∀ (vec : Fin 104719230 ⊕ Fin 3217907 → ZMod 2) (a : ℕ), a < 1771 → True)
    (v : Fin 104719230 → ZMod 2) (w : Fin 104719230) :
    ((List.range 1771).flatMap (blk2 (toNB ch0O))).foldl scalarStepH
      (((List.range 1771).flatMap (blk1 (toNB ch0O))).foldl scalarStepH
        (Sum.elim v fun _ => 0)) (.inl (net0O.ρ w)) = v w := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
