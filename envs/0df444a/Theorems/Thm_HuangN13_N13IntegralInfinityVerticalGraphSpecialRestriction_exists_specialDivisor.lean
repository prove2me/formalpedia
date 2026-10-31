-- Prove2me | Theorems.Thm_HuangN13_N13IntegralInfinityVerticalGraphSpecialRestriction_exists_specialDivisor
-- name    : HuangN13.N13IntegralInfinityVerticalGraphSpecialRestriction.exists_specialDivisor
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:20:55.465069+00:00
-- url     : https://prove2.me/theorems/1089205b-7b42-4f90-aaa2-d244594f2d54
-- title:
--   exists specialDivisor
-- statement:
--   Exact transplant of the original proof of MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.exists_specialDivisor from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit9 lines10629–10676, command SHA-256 d7bd0587fec4c210a7963420c1ed6929ef88f75e6d248fff951f6b41c851e4bc.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityGraphLineCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial
open scoped Sym2
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13IntegralInfinityVerticalGraphSpecialRestriction.exists_specialDivisor
    (u : MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.R₂[X])
    (E : MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.VerticalGraph)
    (hu : u.Monic)
    (huDegree : u.natDegree = 2)
    (hmDegree : E.m.natDegree = 2)
    (huMem :
      MazurProof.N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal) :
    ∃ Δ : MazurProof.N13SpecialDivisorCharts.EffectiveDivisorTwo,
      MazurProof.N13TwoChartSpecialRestriction.restrict
          (MazurProof.N13IntegralInfinityVerticalGraphTwoChart.twoChartLine
            u E hu huDegree hmDegree huMem) =
        MazurProof.N13SpecialDivisorCharts.ofDivisor Δ := by sorry
