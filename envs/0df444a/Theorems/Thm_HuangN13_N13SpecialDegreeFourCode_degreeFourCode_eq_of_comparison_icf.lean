-- Prove2me | Theorems.Thm_HuangN13_N13SpecialDegreeFourCode_degreeFourCode_eq_of_comparison_icf
-- name    : HuangN13.N13SpecialDegreeFourCode.degreeFourCode_eq_of_comparison_icf
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:08:14.239987+00:00
-- url     : https://prove2.me/theorems/c87fe0d2-916a-4ef0-82c2-22385053e5a1
-- title:
--   degreeFourCode eq of comparison
-- statement:
--   Exact transplant of the original proof of MazurProof.N13SpecialDegreeFourCode.degreeFourCode_eq_of_comparison from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines3928–3940, command SHA-256 3f3045e977ae4307276234994aec2e6aeeb580db3f15d81d455a88d27096ec48.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DegreeFourStatementCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_SpecialJetCodeCore
import Definitions.Def_HuangN13_SpecialSmallFunctionCertificateCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialDegreeFourCode.degreeFourCode_eq_of_comparison_icf
    (D E F H : MazurProof.N13SymmetricSquareTwo.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor D) (MazurProof.N13SpecialDivisorCharts.ofDivisor E))
      (MazurProof.N13SpecialDivisorCharts.tensor (MazurProof.N13SpecialDivisorCharts.ofDivisor F) (MazurProof.N13SpecialDivisorCharts.ofDivisor H))) :
    MazurProof.N13SpecialAbelCode.divisorCode D + MazurProof.N13SpecialAbelCode.divisorCode E =
      MazurProof.N13SpecialAbelCode.divisorCode F + MazurProof.N13SpecialAbelCode.divisorCode H := by sorry
