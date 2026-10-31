-- Prove2me | Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_infinity_sheet_difference
-- name    : HuangN13.N13SpecialDegreeFourCode.infinity_sheet_difference
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:11:37.954023+00:00
-- url     : https://prove2.me/theorems/0497125b-7d4b-43fb-bb79-06a4a3c59d74
-- title:
--   infinity sheet difference
-- statement:
--   Transport the coherent comparison to each infinity branch and apply order additivity to its nonzero factors. The cleared numerator contributes the same tensor-polynomial degree on both branches. Subtract the two balance equations to cancel this degree and identify the difference of the infinity orders with the difference of the tensor-order counts.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines3891-3904, command SHA-256 9d06369d1864b5fcb3f8781a286df87451ce8333d71a183549f14cd97cd58bc3.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_SpecialLaurentBranchesCore
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore
import Definitions.Def_HuangN13_SixLocalOrdersCore
import Definitions.Def_HuangN13_ComparisonOrdersCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialDegreeFourCode.infinity_sheet_difference
    (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H)))
    (z : MazurProof.N13SpecialLaurentBranches.R) (hz : z ≠ 0)
    (hcross : h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) = h.aDen * z) :
    (MazurProof.N13SpecialLaurentBranches.plus z).order - (MazurProof.N13SpecialLaurentBranches.minus z).order =
      ((MazurProof.N13SpecialDivisorBranchOrders.tensorOrder false F H : ℤ) - MazurProof.N13SpecialDivisorBranchOrders.tensorOrder true F H) -
        ((MazurProof.N13SpecialDivisorBranchOrders.tensorOrder false D E : ℤ) - MazurProof.N13SpecialDivisorBranchOrders.tensorOrder true D E) := by sorry
