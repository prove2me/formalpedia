-- Prove2me | Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_exists_saturated_data_of_distinct_split
-- name    : HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_distinct_split
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:34:05.966894+00:00
-- url     : https://prove2.me/theorems/8c9aee3a-b487-470c-b937-ba06b3010d29
-- title:
--   exists saturated data of distinct split
-- statement:
--   Realize the two split affine points by their actual proper point lines, retaining multiplicity when the roots coincide. Their tensor has the required generic Mumford ideal. The two special restriction identities identify its reduced divisor, and the saturation and marking provider supplies the remaining integral conditions. Form the original Data record and transport its generic raw and Picard identities.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines2281–2316, command SHA-256 73c33f4ff6b1772182b03755e987c93a07712a5eb274c07eaa5188bfb6caf091. Four exact imported-lemma references are replaced with provider projections; all mathematical steps remain those of the original source.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_OverlapBranchMapsCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT MazurProof.N13ProperCurveReduction.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_distinct_split
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13MarkedQuadraticExistence.Model)
    (hdeg : D.u.natDegree = 2)
    (x₁ x₂ : MazurProof.N13SplitQuadraticSpecialRestriction.Q₂)
    (hfactor :
      D.u = (Polynomial.X - Polynomial.C x₁) *
        (Polynomial.X - Polynomial.C x₂))
    (hneq : x₁ ≠ x₂) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data,
      MazurProof.N13TwoChartPicardRealization.genericRaw
          R.charts R.infinityOrder =
        MazurProof.SexticMumford.mumfordRaw MazurProof.N13MarkedQuadraticExistence.Model D ∧
      R.toGenericPic =
        MazurProof.SexticMumford.classOf
          MazurProof.N13MarkedQuadraticExistence.Model
          (MazurProof.N13Infinity.positiveInfinityOrder
            MazurProof.N13TwoChartPicardRealization.Q₂)
          D ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts 0 0 := by sorry
