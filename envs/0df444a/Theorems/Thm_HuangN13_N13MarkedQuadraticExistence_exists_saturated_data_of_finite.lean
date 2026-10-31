-- Prove2me | Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_exists_saturated_data_of_finite
-- name    : HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_finite
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:36:19.225575+00:00
-- url     : https://prove2.me/theorems/888834ca-bcf1-4a1c-a5db-39d0674b3c4f
-- title:
--   exists saturated data of finite
-- statement:
--   Exact transplant of the original proof of MazurProof.N13MarkedQuadraticExistence.exists_saturated_data_of_finite from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines1906–1961, command SHA-256 afcea80e7ae62e24ac8823fb0e0827f8a149e41147e98148c10aa67cec3ccc10.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SpecialComparisonCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_finite
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13MarkedQuadraticExistence.Model)
    (hdeg : D.u.natDegree = 2)
    (hfinite :
      Module.Finite MazurProof.N13FiniteAffineTwoChart.R₂
        (MazurProof.N13FiniteAffineTwoChart.AffineCurve ⧸
          MazurProof.N13FiniteAffineTwoChart.finiteAffineIdeal D.toSemi)) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data,
      MazurProof.N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        MazurProof.SexticMumford.mumfordRaw MazurProof.N13MarkedQuadraticExistence.Model D ∧
      R.toGenericPic =
        MazurProof.SexticMumford.classOf
          MazurProof.N13MarkedQuadraticExistence.Model
          (MazurProof.N13Infinity.positiveInfinityOrder MazurProof.N13MarkedQuadraticExistence.Q₂)
          D ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts 0 0 := by sorry
