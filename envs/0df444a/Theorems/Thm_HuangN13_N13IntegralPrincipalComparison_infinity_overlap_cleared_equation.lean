-- Prove2me | Theorems.Thm_HuangN13_N13IntegralPrincipalComparison_infinity_overlap_cleared_equation
-- name    : HuangN13.N13IntegralPrincipalComparison.infinity_overlap_cleared_equation
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:25:25.940759+00:00
-- url     : https://prove2.me/theorems/0bf7b248-e2aa-4340-a555-7655ba363db5
-- title:
--   infinity overlap cleared equation
-- statement:
--   Map the affine cleared equation into the ordinary overlap chart, then substitute the given cross-multiplication identity. The line compatibility identifies each localized infinity ideal with its affine ideal. The affine denominator b has nonzero image, so cancel its nonzero principal ideal after passing to the fraction field and reflect the resulting equality back to the overlap ideals.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines1776-1794, command SHA-256 8fea154ff43b0188eb0bef5c0bb1fbcfc1d361c5d4c782417a599bdff14c98ce.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13IntegralPrincipalComparison.infinity_overlap_cleared_equation
    (L M : MazurProof.N13TwoChartPicardRealization.Line) (a b : MazurProof.N13OverlapBranchCompatibility.A) (c d : MazurProof.N13OverlapBranchCompatibility.B) (hb : b ≠ 0)
    (haffine : Ideal.span ({a} : Set MazurProof.N13OverlapBranchCompatibility.A) * L.affineIdeal =
      Ideal.span ({b} : Set MazurProof.N13OverlapBranchCompatibility.A) * M.affineIdeal)
    (hcross : MazurProof.N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O d =
      MazurProof.N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O c) :
    Ideal.map (algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O) (Ideal.span ({c} : Set MazurProof.N13OverlapBranchCompatibility.B) * L.infinityIdeal) =
      Ideal.map (algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O) (Ideal.span ({d} : Set MazurProof.N13OverlapBranchCompatibility.B) * M.infinityIdeal) := by sorry
