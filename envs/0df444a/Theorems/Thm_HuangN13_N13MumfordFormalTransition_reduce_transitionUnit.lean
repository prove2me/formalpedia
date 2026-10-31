-- Prove2me | Theorems.Thm_HuangN13_N13MumfordFormalTransition_reduce_transitionUnit
-- name    : HuangN13.N13MumfordFormalTransition.reduce_transitionUnit
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:31:29.90225+00:00
-- url     : https://prove2.me/theorems/37260256-ea65-433c-97fb-ecb0148e6354
-- title:
--   reduce transitionUnit
-- statement:
--   Exact transplant of the original proof of MazurProof.N13MumfordFormalTransition.reduce_transitionUnit from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines4807–4839, command SHA-256 ca75ae8ada65dce7f1d9d3b58b0bbaf0881e2a023bcfda68232fcf42749f34b8.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore

set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13MumfordFormalTransition.reduce_transitionUnit
    (D : MazurProof.N13MumfordFormalTransition.NearBaseMumford) :
    MazurProof.N13FormalLineBundleCech.reduceOverlap
        (MazurProof.N13FormalCurveOverlap.toOverlap
          (MazurProof.N13MumfordFormalTransition.transitionUnit D : MazurProof.N13MumfordFormalTransition.FormalCurve)) =
      MazurProof.N13FormalLineBundleCech.oneOverlap (R := MazurProof.N13MumfordFormalTransition.K) := by sorry
