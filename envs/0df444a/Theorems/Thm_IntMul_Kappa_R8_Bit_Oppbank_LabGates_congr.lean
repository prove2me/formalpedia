-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_LabGates_congr
-- name    : IntMul.Kappa.R8.Bit.Oppbank.LabGates_congr
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T21:44:45.497271+00:00
-- url     : https://prove2.me/theorems/2b86f3d4-d9ff-47bb-a785-54520b29d245
-- title:
--   LabGates depends only on labels of touched wires
-- statement:
--   If two labelings $L,L'$ agree on every wire touched by an instruction list $\ell$, then $\mathrm{LabGates}\,N\,\ell\,L$ if and only if $\mathrm{LabGates}\,N\,\ell\,L'$.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit (LabGates FMat Instr)
theorem LabGates_congr {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {R : Type*} [CommRing R]
    {m N : ℕ} (l : List (Instr Wr R m)) (L L' : Wr → FMat m N)
    (h : ∀ w, (∃ i ∈ l,
      match i with
      | .gate _ S => w ∈ S
      | .edge w' _ => w = w') → L w = L' w) :
    LabGates N l L ↔ LabGates N l L' := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
