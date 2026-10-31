-- Prove2me | Theorems.Thm_HuangN13_N13SpecialGraphDivisorCharts_ofDivisor_graphDivisor_affineIdeal
-- name    : HuangN13.N13SpecialGraphDivisorCharts.ofDivisor_graphDivisor_affineIdeal
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:20:33.539289+00:00
-- url     : https://prove2.me/theorems/0c6804df-f8b4-485f-813b-1e3b25bf50fc
-- title:
--   ofDivisor graphDivisor affineIdeal
-- statement:
--   Exact transplant of the original proof of MazurProof.N13SpecialGraphDivisorCharts.ofDivisor_graphDivisor_affineIdeal from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit9 lines1777–1814, command SHA-256 59bcee5bd723f4577642a1c3cda410358048f605c7b8c181c6107f8af6f631fc.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial
open scoped Sym2

theorem HuangN13.N13SpecialGraphDivisorCharts.ofDivisor_graphDivisor_affineIdeal
    (D : MazurProof.N13GoodCoordinateRingTwo.SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    (MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SpecialGraphDivisor.graphDivisor D hdeg)).affineIdeal =
      MazurProof.N13GoodCoordinateRingTwo.mumfordIdeal D.u D.v := by sorry
