-- Prove2me | Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_infinity_sheet_difference_icf
-- name    : HuangN13.N13SpecialDegreeFourCode.infinity_sheet_difference_icf
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:38:35.144564+00:00
-- url     : https://prove2.me/theorems/593a3695-a4ec-46a8-8ea1-2666351e593a
-- title:
--   infinity sheet difference
-- statement:
--   Exact transplant of the original proof of MazurProof.N13SpecialDegreeFourCode.infinity_sheet_difference from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines3891–3904, command SHA-256 9d06369d1864b5fcb3f8781a286df87451ce8333d71a183549f14cd97cd58bc3.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DegreeFourStatementCore
import Definitions.Def_HuangN13_SpecialComparisonCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialDegreeFourCode.infinity_sheet_difference_icf
    (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H)))
    (z : MazurProof.N13SpecialLaurentBranches.R) (hz : z ≠ 0)
    (hcross : h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) = h.aDen * z) :
    (MazurProof.N13SpecialLaurentBranches.plus z).order - (MazurProof.N13SpecialLaurentBranches.minus z).order =
      ((MazurProof.N13SpecialDivisorBranchOrders.tensorOrder false F H : ℤ) - MazurProof.N13SpecialDivisorBranchOrders.tensorOrder true F H) -
        ((MazurProof.N13SpecialDivisorBranchOrders.tensorOrder false D E : ℤ) - MazurProof.N13SpecialDivisorBranchOrders.tensorOrder true D E) := by sorry
