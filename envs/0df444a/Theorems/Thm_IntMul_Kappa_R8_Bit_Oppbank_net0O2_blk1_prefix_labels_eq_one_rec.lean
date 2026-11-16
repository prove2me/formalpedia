-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk1_prefix_labels_eq_one_rec
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_blk1_prefix_labels_eq_one_rec
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:31:21.525543+00:00
-- url     : https://prove2.me/theorems/91f90370-4776-469e-91c7-943d3b6ba8d4
-- title:
--   Prefix labels of blk1 stay at 1 on touched wires (QHNetRec)
-- statement:
--   On the total-decoder network `QHNetRec`, the stage-one block \(\mathrm{blk1}\) leaves the constant-\(1\) labelling unchanged at every wire it touches, when the labelling is computed only on the preceding banks.
--
--   Let \(N\) be a field size at which the packed edge family \(\mathrm{EOKO}(\mathrm{ch0NB},N)\) holds, and fix a bank index \(i<1771\). Write \(L_i\) for the labelling obtained by folding \(\mathrm{labStepH}_N\) along the flattened prefix \(\mathrm{flatMap}(\mathrm{blk1}(\mathrm{toNB}(\mathrm{ch0O})),[0..i))\) starting from the constant map \(w\mapsto 1\). If a global wire \(w\) is touched by a gate support or an edge of \(\mathrm{blk1}(\mathrm{toNB}(\mathrm{ch0O}),i)\), then
--
--   $$
--   L_i(w)=1.
--   $$
--
--   The reason is that earlier banks \(b<i\) touch only the disjoint fibres \(\iota_1(b)(\ell)\) (injectivity of \(g_1\) and of the decoder \(g_w\)), so no earlier edge can update the label at a wire of bank \(i\).
--
--   **Formalization Note.** The statement is identical to `net0O2_blk1_prefix_labels_eq_one`, with preamble importing the Rec packs `EOKOPack2Rec`, `OneRun2Rec`, and `QHNetRec` rather than `EOKOPack2`, `OneRun2`, and `QHNet`. Solutions may import the Rec theorems `g1_inj_rec`, `g1_lt_rec`, `gw_inj_rec`, and `net0O2_blk1_touch_iota1_lt_rec`. It does not close or replace `7305eada-bd2d-4968-bcc6-24ff3d533141`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK densify: prefix labels of blk1 stay at 1, restated on the Rec packs QHNetRec (d127abea), OneRun2Rec (a4df37e2), EOKOPack2Rec (8ba6deb1). Does not close or replace 7305eada-bd2d-4968-bcc6-24ff3d533141.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2Rec
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2Rec
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
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
theorem net0O2_blk1_prefix_labels_eq_one_rec (N : ℕ) (_h : EOKO ch0NB N)
    (i : ℕ) (_hi : i < 1771) (w : Fin 104719230 ⊕ Fin 3217907)
    (_hw : ∃ instr ∈ blk1 (toNB ch0O) i,
      match instr with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') :
    ((List.range i).flatMap (blk1 (toNB ch0O))).foldl (labStepH N) (fun _ => (1 : FMat 529 N)) w = 1 := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
