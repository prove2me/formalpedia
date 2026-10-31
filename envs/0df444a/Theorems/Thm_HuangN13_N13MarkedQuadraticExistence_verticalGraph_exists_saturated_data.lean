-- Prove2me | Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_verticalGraph_exists_saturated_data
-- name    : HuangN13.N13MarkedQuadraticExistence.verticalGraph_exists_saturated_data
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:51:46.85847+00:00
-- url     : https://prove2.me/theorems/0369c041-0209-4cfe-a045-a662fbfe8ca2
-- title:
--   verticalGraph exists saturated data
-- statement:
--   Exact transplant of the original proof of MazurProof.N13MarkedQuadraticExistence.verticalGraph_exists_saturated_data from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines2068–2158, command SHA-256 419b9c1473ed8031b3d0bae6ab93b1e5707ebb273323f58edb7c7ea2b0d054db.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_ReciprocalPolynomialFactsCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13MarkedQuadraticExistence.verticalGraph_exists_saturated_data
    {D : MazurProof.SexticMumford.Mumford
      MazurProof.N13IrreducibleQuadraticSpread.Model}
    {a b : MazurProof.N13IrreducibleQuadraticSpread.R₂}
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
    (hm :
      (X ^ 2 +
          C (a : MazurProof.N13IrreducibleQuadraticSpread.Q₂) * X +
          C (b : MazurProof.N13IrreducibleQuadraticSpread.Q₂) :
        MazurProof.N13IrreducibleQuadraticSpread.Q₂[X]) =
        X ^ 2 +
          C (D.u.coeff 1 / D.u.coeff 0) * X +
          C ((D.u.coeff 0)⁻¹))
    (E : MazurProof.N13IntegralInfinityVerticalGraphJacobian.VerticalGraph)
    (hmDegree : E.m.natDegree = 2)
    (hI :
      MazurProof.N13ReciprocalInfinityContraction.integralInfinityIdeal
          D hdeg h0 =
        E.ideal) :
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
