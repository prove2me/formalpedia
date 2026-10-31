-- Prove2me | Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_weightedLocalCode_eq_code_difference_icf
-- name    : HuangN13.N13SpecialDegreeFourCode.weightedLocalCode_eq_code_difference_icf
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:00:27.719135+00:00
-- url     : https://prove2.me/theorems/796ab6e3-ea46-4226-9750-e8273ac734da
-- title:
--   weightedLocalCode eq code difference
-- statement:
--   Exact transplant of the original proof of MazurProof.N13SpecialDegreeFourCode.weightedLocalCode_eq_code_difference from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines3906–3926, command SHA-256 ad1685c8bfe9bb8072087e37907844554328286cf455e961318fda04d739ee4c.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DegreeFourStatementCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialDegreeFourCode.weightedLocalCode_eq_code_difference_icf
    (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H)))
    (z : MazurProof.N13SpecialLaurentBranches.R) (hz : z ≠ 0)
    (hcross : h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) = h.aDen * z) :
    MazurProof.N13SpecialSixJetOrders.weightedLocalCode z =
      (MazurProof.N13SpecialAbelCode.divisorCode F + MazurProof.N13SpecialAbelCode.divisorCode H) -
        (MazurProof.N13SpecialAbelCode.divisorCode D + MazurProof.N13SpecialAbelCode.divisorCode E) := by sorry
