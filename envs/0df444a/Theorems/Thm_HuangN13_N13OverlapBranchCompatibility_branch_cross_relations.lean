-- Prove2me | Theorems.Thm_HuangN13_N13OverlapBranchCompatibility_branch_cross_relations
-- name    : HuangN13.N13OverlapBranchCompatibility.branch_cross_relations
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:36:19.538236+00:00
-- url     : https://prove2.me/theorems/bf49a19a-1ff1-4892-8a8e-3556cdd6cdd6
-- title:
--   A common overlap fraction gives the same cross relation on both branches
-- statement:
--   Apply the positive and negative overlap homomorphisms to the same given cross-multiplication identity. The original compatibility lemmas identify their values on affine functions with the two Laurent expansions and their values on infinity functions with the corresponding power-series expansions. Multiplicativity then gives both exact branch cross relations, using the same four functions on both branches.
-- source:
--   Xiang Huang, Apache-2.0. Original source: https://github.com/xiangyazi24/FLT/blob/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof/N13OverlapBranchCompatibility.lean. Exact flattened unit18 lines1988-2005, source-command SHA-256 1157073c074fa198075191232f667d96fe41f5d89ff040f2e13406ef248c74e8. Original-file line mapping is not asserted.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13OverlapBranchCompatibility.branch_cross_relations (a b : MazurProof.N13OverlapBranchCompatibility.A) (c d : MazurProof.N13OverlapBranchCompatibility.B)
    (h : MazurProof.N13OrdinaryCurveOverlap.affineToInfinityOverlap a * algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O d =
      MazurProof.N13OrdinaryCurveOverlap.affineToInfinityOverlap b * algebraMap MazurProof.N13OverlapBranchCompatibility.B MazurProof.N13OverlapBranchCompatibility.O c) :
    MazurProof.N13Infinity.coordinateToLaurent MazurProof.N13OverlapBranchCompatibility.Q₂ (MazurProof.N13IntegralFractionalHull.integralToRational a) *
        MazurProof.N13OverlapBranchCompatibility.includePower (MazurProof.N13InfinityChartMarking.positiveExpansion d) =
      MazurProof.N13Infinity.coordinateToLaurent MazurProof.N13OverlapBranchCompatibility.Q₂ (MazurProof.N13IntegralFractionalHull.integralToRational b) *
        MazurProof.N13OverlapBranchCompatibility.includePower (MazurProof.N13InfinityChartMarking.positiveExpansion c) ∧
    MazurProof.N13InfinityMinus.coordinateToLaurentMinus MazurProof.N13OverlapBranchCompatibility.Q₂ (MazurProof.N13IntegralFractionalHull.integralToRational a) *
        MazurProof.N13OverlapBranchCompatibility.includePower (MazurProof.N13InfinityChartMarking.negativeExpansion d) =
      MazurProof.N13InfinityMinus.coordinateToLaurentMinus MazurProof.N13OverlapBranchCompatibility.Q₂ (MazurProof.N13IntegralFractionalHull.integralToRational b) *
        MazurProof.N13OverlapBranchCompatibility.includePower (MazurProof.N13InfinityChartMarking.negativeExpansion c) := by sorry
