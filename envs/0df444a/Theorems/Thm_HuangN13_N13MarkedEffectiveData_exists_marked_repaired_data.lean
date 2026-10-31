-- Prove2me | Theorems.Thm_HuangN13_N13MarkedEffectiveData_exists_marked_repaired_data
-- name    : HuangN13.N13MarkedEffectiveData.exists_marked_repaired_data
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:21:31.514797+00:00
-- url     : https://prove2.me/theorems/8ce501c9-0d4d-4d2b-a764-e43f7905a4e4
-- title:
--   exists marked repaired data
-- statement:
--   Exact transplant of the original proof of MazurProof.N13MarkedEffectiveData.exists_marked_repaired_data from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines2589–2603, command SHA-256 a5f4be7ac6e3b168f6ad8b3666aff63199a52d1e6b01b074d9918e948fbcfcfa.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13MarkedEffectiveData.exists_marked_repaired_data (D : MazurProof.N13Mumford.Mumford MazurProof.N13TwoChartPicardRealization.Q₂) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data,
      MazurProof.N13TwoChartPicardRealization.genericRaw R.charts R.infinityOrder =
        MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model (MazurProof.N13EffectiveInfinityRepair.repair D) ∧
      R.toGenericPic = MazurProof.SexticMumford.classOf MazurProof.N13TwoChartPicardRealization.Model
        (MazurProof.N13Infinity.positiveInfinityOrder MazurProof.N13TwoChartPicardRealization.Q₂) D ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts
        (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity (MazurProof.N13EffectiveInfinityRepair.repair D)) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity (MazurProof.N13EffectiveInfinityRepair.repair D)) := by sorry
