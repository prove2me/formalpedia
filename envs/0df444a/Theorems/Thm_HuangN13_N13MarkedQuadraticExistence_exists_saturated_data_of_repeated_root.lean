-- Prove2me | Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_exists_saturated_data_of_repeated_root
-- name    : HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_repeated_root
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:33:52.585374+00:00
-- url     : https://prove2.me/theorems/e13b61e4-b00d-495f-bb14-4742be2f10dc
-- title:
--   exists saturated data of repeated root
-- statement:
--   Realize the two split affine points by their actual proper point lines, retaining multiplicity when the roots coincide. Their tensor has the required generic Mumford ideal. The two special restriction identities identify its reduced divisor, and the saturation and marking provider supplies the remaining integral conditions. Form the original Data record and transport its generic raw and Picard identities.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines2370–2402, command SHA-256 82253e49d952052b16c8f9500af2edb305e0257f262811dab5453d184f86b7b9. Four exact imported-lemma references are replaced with provider projections; all mathematical steps remain those of the original source.

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

theorem HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_repeated_root
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13MarkedQuadraticExistence.Model)
    (x : MazurProof.N13SplitQuadraticSpecialRestriction.Q₂)
    (hfactor :
      D.u = (Polynomial.X - Polynomial.C x) ^ 2) :
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
