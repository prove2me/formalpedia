-- Prove2me | Theorems.Thm_HuangN13_N13PrimitiveAffineComparison_integral_cleared_equation
-- name    : HuangN13.N13PrimitiveAffineComparison.integral_cleared_equation
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:10:32.32833+00:00
-- url     : https://prove2.me/theorems/0232fb2e-e0de-48a7-9e2c-be0ca05facf4
-- title:
--   A primitive generic principal relation gives the integral cleared affine equation
-- statement:
--   The generic principal-ideal relation gives equality of the two cleared affine ideals after passing to the rational coordinate ring. Nonzero reduction of a and b makes their principal ideals saturated by powers of two. Combine that saturation with the vertical saturation of the original two line ideals. Any localized membership relation then has a nonzero two-adic scalar denominator that can be cancelled. Descending in both directions gives equality of the integral cleared affine ideals.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines1097-1130, command SHA-256 a6e8a50108c7951943ac31e6f7419fcd897e63cf5cfa033db90c125adb96f32b.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13PrimitiveAffineComparison.instAlgebraAR MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13PrimitiveAffineComparison.integral_cleared_equation
    (L M : MazurProof.N13TwoChartPicardRealization.Line)
    (hL : MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated L) (hM : MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated M)
    (f : MazurProof.N13PrincipalBranchIdeals.Fˣ) (n m : ℕ) (a b : MazurProof.N13OverlapBranchCompatibility.A)
    (ha : MazurProof.N13GeneralizedMumfordReduction.reduceCoordinate a ≠ 0)
    (hb : MazurProof.N13GeneralizedMumfordReduction.reduceCoordinate b ≠ 0)
    (hf : (2 : MazurProof.N13PrincipalBranchIdeals.F) ^ m * (f : MazurProof.N13PrincipalBranchIdeals.F) * algebraMap MazurProof.N13OverlapBranchCompatibility.A MazurProof.N13PrincipalBranchIdeals.F b =
      (2 : MazurProof.N13PrincipalBranchIdeals.F) ^ n * algebraMap MazurProof.N13OverlapBranchCompatibility.A MazurProof.N13PrincipalBranchIdeals.F a)
    (hprincipal : MazurProof.N13TwoChartPicardRealization.genericIdealUnit L * toPrincipalIdeal MazurProof.N13PrincipalBranchIdeals.R MazurProof.N13PrincipalBranchIdeals.F f = MazurProof.N13TwoChartPicardRealization.genericIdealUnit M) :
    Ideal.span ({a} : Set MazurProof.N13OverlapBranchCompatibility.A) * L.affineIdeal =
      Ideal.span ({b} : Set MazurProof.N13OverlapBranchCompatibility.A) * M.affineIdeal := by sorry
