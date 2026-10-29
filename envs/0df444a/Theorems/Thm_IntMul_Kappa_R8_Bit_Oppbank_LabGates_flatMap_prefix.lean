-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_LabGates_flatMap_prefix
-- name    : IntMul.Kappa.R8.Bit.Oppbank.LabGates_flatMap_prefix
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T20:37:37.145382+00:00
-- url     : https://prove2.me/theorems/6aaa644b-bad5-4e56-9ecb-258a1c3010f8
-- title:
--   LabGates of flatMap from per-prefix label states
-- statement:
--   Let \(\mathtt{blk}:\mathbb{N}\to\mathrm{List}(\mathrm{Instr})\) and fix an initial frame labeling \(L\). Write \(P_i=(\mathrm{List.range}\,i).\mathrm{flatMap}\,\mathtt{blk}\) for the prefix program.
--
--   If for every \(i<k\) the block \(\mathtt{blk}(i)\) is label-gate consistent from the labeling produced by running \(P_i\) on \(L\), then the full concatenation is label-gate consistent from \(L\):
--
--   $$
--   \mathrm{LabGates}\,N\,((\mathrm{List.range}\,k).\mathrm{flatMap}\,\mathtt{blk})\,L.
--   $$
--
--   This is the correct composition principle for assembling stage-one/stage-two `LabGates` of `net0O.prog`.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192

namespace IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R6.Bit (LabGates labStepH FMat)
theorem LabGates_flatMap_prefix {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {R : Type*} [CommRing R]
    {m N k : ℕ} (blk : ℕ → List (IntMul.Kappa.R6.Bit.Instr Wr R m))
    (L : Wr → FMat m N)
    (h : ∀ (i : ℕ), i < k →
      LabGates N (blk i) (((List.range i).flatMap blk).foldl (labStepH N) L)) :
    LabGates N ((List.range k).flatMap blk) L := by sorry
end IntMul.Kappa.R8.Bit.Oppbank
