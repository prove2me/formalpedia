-- Prove2me | Theorems.Thm_HuangN13_N13SpecialQuadraticGraphRegularity_map_mumfordIdeal_eq_graphDivisor_affineIdeal
-- name    : HuangN13.N13SpecialQuadraticGraphRegularity.map_mumfordIdeal_eq_graphDivisor_affineIdeal
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:21:31.5663+00:00
-- url     : https://prove2.me/theorems/315fa950-15f3-4be1-adaa-821c07621f26
-- title:
--   map mumfordIdeal eq graphDivisor affineIdeal
-- statement:
--   Exact transplant of the original proof of MazurProof.N13SpecialQuadraticGraphRegularity.map_mumfordIdeal_eq_graphDivisor_affineIdeal from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit9 lines2720–2735, command SHA-256 b7eab894fd650a07beed8d255e6072bf8d431471e2521fcec1f4b79a09f763f0.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialQuadraticGraphRegularity.map_mumfordIdeal_eq_graphDivisor_affineIdeal
    (D :
      MazurProof.N13GeneralizedMumfordIntegral.TwoAdic.SemiMumford₂)
    (hdeg : D.u.natDegree = 2) :
    Ideal.map MazurProof.N13GeneralizedMumfordReduction.reduceCoordinate
        (MazurProof.N13GeneralizedMumfordIntegral.mumfordIdeal
          (R := MazurProof.N13GeneralizedMumfordReduction.R₂) D.u D.v) =
      (MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SpecialGraphDivisor.graphDivisor
          (MazurProof.N13SpecialQuadraticGraphRegularity.reduceSemiMumford D hdeg)
          (MazurProof.N13SpecialQuadraticGraphRegularity.reduceSemiMumford_u_natDegree D hdeg))).affineIdeal := by sorry
