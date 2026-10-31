-- Prove2me | Theorems.Thm_HuangN13_N13SpecialInfinityGraphDivisorCharts_ofDivisor_graphDivisor_infinityIdeal
-- name    : HuangN13.N13SpecialInfinityGraphDivisorCharts.ofDivisor_graphDivisor_infinityIdeal
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:55:55.884207+00:00
-- url     : https://prove2.me/theorems/41d386c1-2ec3-4941-a126-372629843721
-- title:
--   ofDivisor graphDivisor infinityIdeal
-- statement:
--   Exact transplant of the original proof of MazurProof.N13SpecialInfinityGraphDivisorCharts.ofDivisor_graphDivisor_infinityIdeal from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit9 lines9948–9984, command SHA-256 2f141433d306a89ea3c7566e2b482ec40b0e6e83fef1f360d6558ceea65aaf22.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityGraphLineCore
import Definitions.Def_HuangN13_SpecialComparisonCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialInfinityGraphDivisorCharts.ofDivisor_graphDivisor_infinityIdeal
    (D : MazurProof.N13SpecialInfinityGraphDivisor.SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    (MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SpecialInfinityGraphDivisor.graphDivisor D hdeg)).infinityIdeal =
      MazurProof.N13SpecialInfinityGraphDivisorCharts.graphIdeal D.u D.v := by sorry
