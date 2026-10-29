-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_net0O2_blk1_touch_iota1_lt
-- name    : IntMul.Kappa.R8.Bit.Oppbank.net0O2_blk1_touch_iota1_lt
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T22:21:08.745915+00:00
-- url     : https://prove2.me/theorems/2729b863-b6ee-4a75-bcbf-290ac67ef736
-- title:
--   Touched wires of blk1 lie in the iota1-image below NL
-- statement:
--   Every wire touched by a stage-one block $\mathrm{blk1}(b)$ (gate support or edge target) is the image under the bank embedding $\iota_1(b,\cdot)$ of some local index strictly below $NL=31359$.
--
--   Formally, if $w$ belongs to the support of a gate or is the target of an edge in $\mathrm{blk1}(\mathrm{ch},b)$ with $b<1771$, then
--   $$
--   \exists\, \ell < NL,\qquad w = \iota_1(b,\ell).
--   $$
--
--   This is the wire-membership companion to $g_1$-injectivity: together they give disjointness of stage-one banks, which is what keeps prefix labels at the constant $1$ on later banks.
--
--   Formalization Note. Uses `NB.blk1`, `ι1`, `NL` from the opp-bank QHNet/WireLayout packages; the match on `Instr` mirrors `LabGates_congr` touch hypotheses.
-- source:
--   R8 BitNB FormalOK densify: companion to net0O2_blk1_prefix_labels_eq_one / R6 NB iota1 image of local wires

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit (Instr)
open IntMul.Kappa.R8.Bit.Oppbank.NB
open IntMul.Kappa.R8.Bit.Oppbank (NL)
theorem net0O2_blk1_touch_iota1_lt {ch : Ch} {b : ℕ} (hb : b < 1771)
    (w : Wr)
    (hw : ∃ instr ∈ blk1 ch b,
      match instr with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') :
    ∃ ℓ < NL, w = ι1 b ℓ := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
