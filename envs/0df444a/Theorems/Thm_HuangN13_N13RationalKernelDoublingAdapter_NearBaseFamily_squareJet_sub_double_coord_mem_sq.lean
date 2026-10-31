-- Prove2me | Theorems.Thm_HuangN13_N13RationalKernelDoublingAdapter_NearBaseFamily_squareJet_sub_double_coord_mem_sq
-- name    : HuangN13.N13RationalKernelDoublingAdapter.NearBaseFamily.squareJet_sub_double_coord_mem_sq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:32:26.614721+00:00
-- url     : https://prove2.me/theorems/57cdf9ac-b08f-4d61-8089-407e69b1ac2e
-- title:
--   squareJet sub double coord mem sq
-- statement:
--   Exact transplant of the original proof of MazurProof.N13RationalKernelDoublingAdapter.NearBaseFamily.squareJet_sub_double_coord_mem_sq from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines7148–7159, command SHA-256 7f8785526fe54543926fcf820f8ac515441ca3afda1d85859712c6d2a5f6d78a.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13RationalKernelDoublingAdapter.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13RationalKernelDoublingAdapter.NearBaseFamily.squareJet_sub_double_coord_mem_sq {H : AddSubgroup MazurProof.N13RationalKernelDoublingAdapter.RationalPic}
    (F : MazurProof.N13RationalKernelDoublingAdapter.NearBaseFamily H) (z : H) (i : Fin 2) :
    F.squareJet z i -
        (F.coord z i + F.coord z i) ∈
      MazurProof.N13TwoAdicKernelChart.coordIdeal F.coord z *
        MazurProof.N13TwoAdicKernelChart.coordIdeal F.coord z := by sorry
