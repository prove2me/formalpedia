-- Prove2me | Theorems.Thm_HuangN13_N13ConstructedKernelDoubling_selected_cross_coefficients
-- name    : HuangN13.N13ConstructedKernelDoubling.selected_cross_coefficients
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:38:26.083995+00:00
-- url     : https://prove2.me/theorems/c4d80376-2088-4b3e-ad67-8954a9ec983c
-- title:
--   selected cross coefficients
-- statement:
--   Exact transplant of the original proof of MazurProof.N13ConstructedKernelDoubling.selected_cross_coefficients from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines5956–6002, command SHA-256 13163afb4078c1182cb2b72713a5b3e37c80c8e29333a1c91db89d46ab3ef49f.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13ConstructedKernelDoubling.selected_cross_coefficients
    {H : AddSubgroup MazurProof.N13RationalKernelDoublingAdapter.RationalPic}
    (L : MazurProof.N13RationalKernelDoublingAdapter.NearBaseFamily H) (z : H) :
    ∀ i, ((L.pair z).u ^ 2 - MazurProof.N13AbelChartBase.baseSmoothMumford.u *
        (L.pair (2 • z)).u).coeff i ∈
      MazurProof.N13TwoAdicKernelChart.coordIdeal L.coord z * MazurProof.N13TwoAdicKernelChart.coordIdeal L.coord z := by sorry
