-- Prove2me | Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_ReciprocalGraphClosure_exists_saturated_data
-- name    : HuangN13.N13MarkedQuadraticExistence.ReciprocalGraphClosure.exists_saturated_data
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:55:56.77699+00:00
-- url     : https://prove2.me/theorems/ce92e00e-41a7-436c-871e-64a4c5e85e0e
-- title:
--   exists saturated data
-- statement:
--   Use the actual reciprocal graph closure to construct its proper two-chart line. The special restriction identifies the literal reduced root divisor. Reflection of the reciprocal polynomial identifies the generic Mumford ideal, while the saturation and marking provider supplies the integral conditions. Package those same data and apply the original generic raw and Picard-class identities.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines1963–2066, command SHA-256 483963ccbf34715f07244749a2f72420c835b439c013154c514fc8b66143eb72. Three exact imported-lemma references are replaced with provider projections; all mathematical steps remain those of the original source.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_OverlapBranchMapsCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_InfinityGraphLineCore
import Definitions.Def_HuangN13_ReciprocalPolynomialFactsCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13MarkedQuadraticExistence.ReciprocalGraphClosure.exists_saturated_data
    {D : MazurProof.SexticMumford.Mumford
      MazurProof.N13IrreducibleQuadraticSpread.Model}
    {a b : MazurProof.N13IrreducibleQuadraticSpread.R₂}
    (E : MazurProof.N13IrreducibleQuadraticSpread.ReciprocalGraphClosure D a b)
    (hdeg : D.u.natDegree = 2)
    (h0 : D.u.coeff 0 ≠ 0)
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
