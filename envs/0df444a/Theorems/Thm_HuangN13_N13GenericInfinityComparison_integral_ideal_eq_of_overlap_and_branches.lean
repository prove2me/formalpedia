-- Prove2me | Theorems.Thm_HuangN13_N13GenericInfinityComparison_integral_ideal_eq_of_overlap_and_branches
-- name    : HuangN13.N13GenericInfinityComparison.integral_ideal_eq_of_overlap_and_branches
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T10:08:10.868774+00:00
-- url     : https://prove2.me/theorems/b998c04c-00a7-4b13-9f84-d2f01a733624
-- title:
--   integral ideal eq of overlap and branches
-- statement:
--   The two branch equalities and the equality away from infinity first identify the generic infinity ideals. To descend this equality, localize an integral ideal-membership relation and clear a nonzero two-adic scalar. Invertibility and nonzero reduction allow the original saturation theorem to cancel that scalar. Applying the descent in both directions gives equality of the integral ideals.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines1682-1718, command SHA-256 28b64d1cbbf841c6345dbe40de54e426f91c4937f1b7c7f29643817a72c37227.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13GenericInfinityComparison.integral_ideal_eq_of_overlap_and_branches
    (I J : Ideal MazurProof.N13InfinityBranchJets.B)
    (hI : IsUnit (I : MazurProof.N13IntegralInfinityPointSpread.InfinityFractionalIdeal))
    (hJ : IsUnit (J : MazurProof.N13IntegralInfinityPointSpread.InfinityFractionalIdeal))
    (hIr : Ideal.map MazurProof.N13IntegralInfinityReduction.reduceCoordinate I ≠ ⊥)
    (hJr : Ideal.map MazurProof.N13IntegralInfinityReduction.reduceCoordinate J ≠ ⊥)
    (hp : Ideal.map MazurProof.N13InfinityChartMarking.positiveExpansion I =
      Ideal.map MazurProof.N13InfinityChartMarking.positiveExpansion J)
    (hm : Ideal.map MazurProof.N13InfinityChartMarking.negativeExpansion I =
      Ideal.map MazurProof.N13InfinityChartMarking.negativeExpansion J)
    (hAway :
      Ideal.map (algebraMap MazurProof.N13GenericInfinityComparison.GenericInfinity MazurProof.N13GenericInfinityComparison.GenericOverlap)
          (Ideal.map (algebraMap MazurProof.N13InfinityBranchJets.B MazurProof.N13GenericInfinityComparison.GenericInfinity) I) =
        Ideal.map (algebraMap MazurProof.N13GenericInfinityComparison.GenericInfinity MazurProof.N13GenericInfinityComparison.GenericOverlap)
          (Ideal.map (algebraMap MazurProof.N13InfinityBranchJets.B MazurProof.N13GenericInfinityComparison.GenericInfinity) J)) : I = J := by sorry
