-- Prove2me | Theorems.Thm_HuangN13_N13OverlapBranchCompatibility_overlap_maps_injective
-- name    : HuangN13.N13OverlapBranchCompatibility.overlap_maps_injective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T11:21:39.099017+00:00
-- url     : https://prove2.me/theorems/4e866948-49db-4414-8c48-9db892ac0400
-- title:
--   Both actual overlap branch homomorphisms are injective
-- statement:
--   The positive and negative homomorphisms from the actual ordinary overlap chart to the corresponding Laurent-series field are both injective.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source-owner ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Original injectivity targets are flattened unit18 lines1926–1948 and1950–1972. The final conjunction contains precisely those two original statements.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_OverlapBranchMapsCore

set_option autoImplicit false
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13OverlapBranchCompatibility.overlap_maps_injective : Function.Injective MazurProof.N13OverlapBranchCompatibility.positiveOverlap ∧
    Function.Injective MazurProof.N13OverlapBranchCompatibility.negativeOverlap := by sorry
