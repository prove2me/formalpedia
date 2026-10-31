-- Prove2me | Theorems.Thm_HuangN13_N13SpecialSmallNumerator_comparison_infinity_order_balance
-- name    : HuangN13.N13SpecialSmallNumerator.comparison_infinity_order_balance
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:54:46.812358+00:00
-- url     : https://prove2.me/theorems/3f88fe0e-016c-4b17-bb5e-e77b5fa76ed2
-- title:
--   comparison infinity order balance
-- statement:
--   Exact transplant of the original proof of MazurProof.N13SpecialSmallNumerator.comparison_infinity_order_balance from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit10 lines8483–8492, command SHA-256 a31fffd6f0fcc9db048591ad2b2112880d1f69ed5c4c7331cb0741011aae1788.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DegreeFourStatementCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialSmallNumerator.comparison_infinity_order_balance
    (negative : Bool) (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H))) :
    (MazurProof.N13SpecialLaurentBranches.includeSeries (MazurProof.N13SpecialOverlapBranches.infinityBranch negative h.iNum)).order + (MazurProof.N13SpecialDivisorBranchOrders.tensorOrder negative D E : ℤ) =
      (MazurProof.N13SpecialLaurentBranches.includeSeries (MazurProof.N13SpecialOverlapBranches.infinityBranch negative h.iDen)).order + (MazurProof.N13SpecialDivisorBranchOrders.tensorOrder negative F H : ℤ) := by sorry
