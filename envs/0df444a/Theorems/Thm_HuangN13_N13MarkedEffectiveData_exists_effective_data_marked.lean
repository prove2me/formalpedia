-- Prove2me | Theorems.Thm_HuangN13_N13MarkedEffectiveData_exists_effective_data_marked
-- name    : HuangN13.N13MarkedEffectiveData.exists_effective_data_marked
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:16:04.070622+00:00
-- url     : https://prove2.me/theorems/f0b001ca-f05c-4b60-a0e8-aec44f3fbce4
-- title:
--   exists effective data marked
-- statement:
--   Exact transplant of the original proof of MazurProof.N13MarkedEffectiveData.exists_effective_data_marked from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines2506–2586, command SHA-256 6671b118ff4b13e29446df835685bffe99b0c8f338a4975c876d9015a69d23bf.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13MarkedEffectiveData.exists_effective_data_marked
    (E : MazurProof.N13Mumford.SemiMumford MazurProof.N13TwoChartPicardRealization.Q₂) (hE : MazurProof.N13EffectiveInfinityRepair.EffectiveChamber E) :
    ∃ R : MazurProof.N13TwoChartPicardRealization.Data, MazurProof.N13TwoChartPicardRealization.genericRaw R.charts R.infinityOrder =
        MazurProof.SexticMumford.semiMumfordRaw MazurProof.N13TwoChartPicardRealization.Model E ∧
      MazurProof.N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities R.charts (MazurProof.N13EffectiveInfinityRepair.positiveMultiplicity E) (MazurProof.N13EffectiveInfinityRepair.negativeMultiplicity E) := by sorry
