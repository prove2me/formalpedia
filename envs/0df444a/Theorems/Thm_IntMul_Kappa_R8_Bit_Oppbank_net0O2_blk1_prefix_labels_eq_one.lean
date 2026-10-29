-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk1_prefix_labels_eq_one
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_blk1_prefix_labels_eq_one
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:55:21.101771+00:00
-- url     : https://prove2.me/theorems/7305eada-bd2d-4968-bcc6-24ff3d533141
-- title:
--   Stage-one prefix leaves bank-i touched wires at label 1
-- statement:
--   Under $\mathrm{EOKO}$, after folding stage-one blocks $0,\ldots,i-1$ from constant label $1$, every wire touched by bank $i$'s $\mathrm{blk1}$ still carries label $1$. With $\mathrm{LabGates\_congr}$ this reduces prefix LabGates to LabGates from constant $1$.

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
open IntMul.Kappa.R6.Bit (labStepH FMat Instr)
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open IntMul.Kappa.R8.Bit.Oppbank.NB (blk1)
theorem net0O2_blk1_prefix_labels_eq_one (N : ℕ) (_h : EOKO ch0NB N)
    (i : ℕ) (_hi : i < 1771) (w : Fin 104719230 ⊕ Fin 3217907)
    (_hw : ∃ instr ∈ blk1 (toNB ch0O) i,
      match instr with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') :
    ((List.range i).flatMap (blk1 (toNB ch0O))).foldl (labStepH N) (fun _ => (1 : FMat 529 N)) w = 1 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
