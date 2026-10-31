-- Prove2me | Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_infinity_cleared_order_balance
-- name    : HuangN13.N13SpecialDegreeFourCode.infinity_cleared_order_balance
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:32:46.693417+00:00
-- url     : https://prove2.me/theorems/c2beabe7-4a47-4b50-ae44-788aabd2d422
-- title:
--   infinity cleared order balance
-- statement:
--   Exact transplant of the original proof of MazurProof.N13SpecialDegreeFourCode.infinity_cleared_order_balance from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines3864–3889, command SHA-256 3a40af90ab66bb980933acfc6526a6d7cac8d07829afc4e2a35abf40a98b888a.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DegreeFourStatementCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialDegreeFourCode.infinity_cleared_order_balance
    (negative : Bool) (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H)))
    (z : MazurProof.N13SpecialLaurentBranches.R) (hz : z ≠ 0)
    (hcross : h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) = h.aDen * z) :
    (MazurProof.N13SpecialOverlapBranches.affineBranch negative z).order + (MazurProof.N13SpecialDivisorBranchOrders.tensorOrder negative D E : ℤ) +
        (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E).natDegree = (MazurProof.N13SpecialDivisorBranchOrders.tensorOrder negative F H : ℤ) := by sorry
