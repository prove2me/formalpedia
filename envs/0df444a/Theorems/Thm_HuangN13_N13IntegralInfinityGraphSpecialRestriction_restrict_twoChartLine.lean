-- Prove2me | Theorems.Thm_HuangN13_N13IntegralInfinityGraphSpecialRestriction_restrict_twoChartLine
-- name    : HuangN13.N13IntegralInfinityGraphSpecialRestriction.restrict_twoChartLine
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:00:27.326954+00:00
-- url     : https://prove2.me/theorems/4d5f72bb-149a-488a-8cee-b1e004a7a121
-- title:
--   An integral infinity graph restricts to its canonical special divisor
-- statement:
--   The monic quadratic graph has a canonical two-point root divisor after reduction. The original affine restriction theorem identifies the reduced affine ideal with that divisor’s affine ideal, and the infinity restriction theorem identifies its infinity ideal. Equality of the complete chart pair follows by the original ChartPair extensionality theorem.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit9 lines11069–11087, command SHA-256 2cae7c0d62beea857147dab4d215c1984dd6aaa08cb871a35dd1ef3db300d728.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityGraphLineCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13IntegralInfinityGraphSpecialRestriction.restrict_twoChartLine
    (E : MazurProof.N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : E.u.Monic)
    (hdeg : E.u.natDegree = 2)
    (hdv : E.v.natDegree ≤ 3)
    (hdw : E.w.natDegree ≤ 4) :
    MazurProof.N13TwoChartSpecialRestriction.restrict
        (MazurProof.N13IntegralInfinityGraphTwoChart.twoChartLine
          E (by omega) hdv hdw hu.ne_zero) =
      MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SpecialInfinityGraphDivisor.graphDivisor
          (MazurProof.N13SpecialInfinityGraphDivisor.reduceGraphData E hu)
          (MazurProof.N13SpecialInfinityGraphDivisor.reduceGraphData_u_natDegree
            E hu hdeg)) := by sorry
