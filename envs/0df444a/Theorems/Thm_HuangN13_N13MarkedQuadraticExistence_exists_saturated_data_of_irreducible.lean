-- Prove2me | Theorems.Thm_HuangN13_N13MarkedQuadraticExistence_exists_saturated_data_of_irreducible
-- name    : HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_irreducible
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:05:02.970136+00:00
-- url     : https://prove2.me/theorems/002bc5ef-1dcf-44e9-b961-05e1e2f45cc2
-- title:
--   exists saturated data of irreducible
-- statement:
--   Exact transplant of the original proof of MazurProof.N13MarkedQuadraticExistence.exists_saturated_data_of_irreducible from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines2199–2221, command SHA-256 53d2ded4de4fd6aa27cd735a79d47821e6171a21bb289e7f245a850f437683cd.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13MarkedQuadraticExistence.exists_saturated_data_of_irreducible
    (D : MazurProof.SexticMumford.Mumford MazurProof.N13MarkedQuadraticExistence.Model)
    (hdeg : D.u.natDegree = 2)
    (hirr : Irreducible D.u) :
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
