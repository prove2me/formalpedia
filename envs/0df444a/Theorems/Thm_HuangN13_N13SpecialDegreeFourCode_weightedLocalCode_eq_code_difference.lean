-- Prove2me | Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_weightedLocalCode_eq_code_difference
-- name    : HuangN13.N13SpecialDegreeFourCode.weightedLocalCode_eq_code_difference
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:46:15.211254+00:00
-- url     : https://prove2.me/theorems/75373930-c315-497d-9f01-6033811a8799
-- title:
--   weightedLocalCode eq code difference
-- statement:
--   Use the finite sheet-difference identities at x=0 and x=1 and the infinity sheet-difference identity. Rewrite each divisor code by its finite and infinity order counts, then take the original weighted linear combination with coefficients1,7,8.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines3906-3926, command SHA-256 ad1685c8bfe9bb8072087e37907844554328286cf455e961318fda04d739ee4c.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_SpecialLaurentBranchesCore
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore
import Definitions.Def_HuangN13_SixLocalOrdersCore
import Definitions.Def_HuangN13_ComparisonOrdersCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialDegreeFourCode.weightedLocalCode_eq_code_difference
    (D E F H : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E)) (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H)))
    (z : MazurProof.N13SpecialLaurentBranches.R) (hz : z ≠ 0)
    (hcross : h.aNum * MazurProof.N13GoodCoordinateRingTwo.xClass (MazurProof.N13SpecialComparisonFactorPair.tensorPolynomial D E) = h.aDen * z) :
    MazurProof.N13SpecialSixJetOrders.weightedLocalCode z =
      (MazurProof.N13SpecialAbelCode.divisorCode F + MazurProof.N13SpecialAbelCode.divisorCode H) -
        (MazurProof.N13SpecialAbelCode.divisorCode D + MazurProof.N13SpecialAbelCode.divisorCode E) := by sorry
