-- Prove2me | Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_finite_sheet_difference
-- name    : HuangN13.N13SpecialDegreeFourCode.finite_sheet_difference
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:11:23.249462+00:00
-- url     : https://prove2.me/theorems/d6b86251-cc3d-4113-9a9d-9a0dd4180acf
-- title:
--   finite sheet difference
-- statement:
--   Apply the original cleared comparison order balance on each finite sheet. Both equalities contain the same tensor-polynomial contribution. Subtract them to cancel that contribution and obtain the difference of the finite tensor-order counts.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines3851-3862, command SHA-256 c1cbb431b3c455c258e9ee3a063d99612e7ca836b90b983009a612867c5bbbd6.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_SpecialLaurentBranchesCore
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore
import Definitions.Def_HuangN13_SixLocalOrdersCore
import Definitions.Def_HuangN13_ComparisonOrdersCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialDegreeFourCode.finite_sheet_difference
    (a : MazurProof.N13SpecialLaurentBranches.K) (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H)))
    (z : MazurProof.N13SpecialLaurentBranches.R) (hz : z ≠ 0)
    (hcross : h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) = h.aDen * z) :
    (MazurProof.N13SpecialLaurentBranches.includeSeries (MazurProof.N13SpecialFiniteBranchFaithfulness.finiteBranch a false z)).order - (MazurProof.N13SpecialLaurentBranches.includeSeries (MazurProof.N13SpecialFiniteBranchFaithfulness.finiteBranch a true z)).order =
      ((MazurProof.N13SpecialFinitePointOrders.finiteTensorOrder a false F H : ℤ) - MazurProof.N13SpecialFinitePointOrders.finiteTensorOrder a true F H) -
        ((MazurProof.N13SpecialFinitePointOrders.finiteTensorOrder a false D E : ℤ) - MazurProof.N13SpecialFinitePointOrders.finiteTensorOrder a true D E) := by sorry
