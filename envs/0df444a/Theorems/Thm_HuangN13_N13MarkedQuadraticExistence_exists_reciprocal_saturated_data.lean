-- Prove2me | Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_exists_reciprocal_saturated_data
-- name    : HuangN13.N13MarkedQuadraticExistence.exists_reciprocal_saturated_data
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:58:34.000887+00:00
-- url     : https://prove2.me/theorems/1e27c2b3-a5b8-440a-9b91-549350e8e982
-- title:
--   exists reciprocal saturated data
-- statement:
--   Exact transplant of the original proof of MazurProof.N13MarkedQuadraticExistence.exists_reciprocal_saturated_data from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines2160–2197, command SHA-256 06f55b69498112d456a951402adff246433cb0b7f5444d85e4859120500d6563.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13MarkedQuadraticExistence.exists_reciprocal_saturated_data
    (D : MazurProof.SexticMumford.Mumford
      MazurProof.N13IrreducibleQuadraticSpread.Model)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (a b : MazurProof.N13IrreducibleQuadraticSpread.R₂)
    (hm :
      (X ^ 2 +
          C (a : MazurProof.N13IrreducibleQuadraticSpread.Q₂) * X +
          C (b : MazurProof.N13IrreducibleQuadraticSpread.Q₂) :
        MazurProof.N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹)) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data,
      MazurProof.N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        MazurProof.SexticMumford.mumfordRaw
          MazurProof.N13IrreducibleQuadraticSpread.Model D ∧
      R.toGenericPic =
        MazurProof.SexticMumford.classOf
          MazurProof.N13IrreducibleQuadraticSpread.Model
          (MazurProof.N13Infinity.positiveInfinityOrder
            MazurProof.N13TwoChartPicardRealization.Q₂)
          D ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts 0 0 := by sorry
