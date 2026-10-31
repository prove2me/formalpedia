-- Prove2me | Theorems.Thm_HuangN13_N13IntegralPrincipalComparison_integral_infinity_cleared_equation
-- name    : HuangN13.N13IntegralPrincipalComparison.integral_infinity_cleared_equation
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:45:35.251611+00:00
-- url     : https://prove2.me/theorems/c1a34843-240b-4f0d-b237-f16ba975589f
-- title:
--   integral infinity cleared equation
-- statement:
--   Apply the integral infinity ideal-equality theorem to the two principal multiples of the infinity ideals. Their invertibility and nonzero reductions follow from the original line and coefficient hypotheses; the two branch equalities are given. The independent overlap-equation theorem supplies the required equality away from infinity.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines1847-1871, command SHA-256 cc3a210989d0f5e2675af524691c50d7a0d33d42961a748379b2dbd97436e720.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13IntegralPrincipalComparison.integral_infinity_cleared_equation
    (L M : MazurProof.N13TwoChartPicardRealization.Line) (a b : MazurProof.N13OverlapBranchCompatibility.A) (c d : MazurProof.N13OverlapBranchCompatibility.B) (hb : b ≠ 0)
    (hc : MazurProof.N13IntegralInfinityReduction.reduceCoordinate c ≠ 0)
    (hd : MazurProof.N13IntegralInfinityReduction.reduceCoordinate d ≠ 0)
    (hL : Ideal.map MazurProof.N13IntegralInfinityReduction.reduceCoordinate L.infinityIdeal ≠ ⊥)
    (hM : Ideal.map MazurProof.N13IntegralInfinityReduction.reduceCoordinate M.infinityIdeal ≠ ⊥)
    (haffine : Ideal.span ({a} : Set MazurProof.N13OverlapBranchCompatibility.A) * L.affineIdeal =
      Ideal.span ({b} : Set MazurProof.N13OverlapBranchCompatibility.A) * M.affineIdeal)
    (hcross : MazurProof.N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O d =
      MazurProof.N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O c)
    (hplus : Ideal.map MazurProof.N13InfinityChartMarking.positiveExpansion (Ideal.span ({c} : Set MazurProof.N13OverlapBranchCompatibility.B) * L.infinityIdeal) =
      Ideal.map MazurProof.N13InfinityChartMarking.positiveExpansion (Ideal.span ({d} : Set MazurProof.N13OverlapBranchCompatibility.B) * M.infinityIdeal))
    (hminus : Ideal.map MazurProof.N13InfinityChartMarking.negativeExpansion (Ideal.span ({c} : Set MazurProof.N13OverlapBranchCompatibility.B) * L.infinityIdeal) =
      Ideal.map MazurProof.N13InfinityChartMarking.negativeExpansion (Ideal.span ({d} : Set MazurProof.N13OverlapBranchCompatibility.B) * M.infinityIdeal)) :
    Ideal.span ({c} : Set MazurProof.N13OverlapBranchCompatibility.B) * L.infinityIdeal = Ideal.span ({d} : Set MazurProof.N13OverlapBranchCompatibility.B) * M.infinityIdeal := by sorry
