-- Prove2me | Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_degreeFourCode_eq_of_comparison
-- name    : HuangN13.N13SpecialDegreeFourCode.degreeFourCode_eq_of_comparison
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:09:15.294985+00:00
-- url     : https://prove2.me/theorems/84a8591c-70c6-4729-83af-5b795cd958b1
-- title:
--   degreeFourCode eq of comparison
-- statement:
--   Choose the certified small numerator supplied by the original coherent comparison. Its six jet certificates force zero geometric weighted code. The sheet-difference comparison identifies that code with the difference of the two pairs of divisor codes; zero difference gives the required equality.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines3928-3940, command SHA-256 3f3045e977ae4307276234994aec2e6aeeb580db3f15d81d455a88d27096ec48.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_SpecialLaurentBranchesCore
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore
import Definitions.Def_HuangN13_SixLocalOrdersCore
import Definitions.Def_HuangN13_ComparisonOrdersCore
import Definitions.Def_HuangN13_SpecialJetCodeCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialDegreeFourCode.degreeFourCode_eq_of_comparison
    (D E F H : MazurProof.N13SymmetricSquareTwo.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E))
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H))) :
    MazurProof.N13SpecialAbelCode.divisorCode D + MazurProof.N13SpecialAbelCode.divisorCode E =
      MazurProof.N13SpecialAbelCode.divisorCode F + MazurProof.N13SpecialAbelCode.divisorCode H := by sorry
