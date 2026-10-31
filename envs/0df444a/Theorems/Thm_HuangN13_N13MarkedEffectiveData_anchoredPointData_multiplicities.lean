-- Prove2me | Theorems.Thm_HuangN13_N13MarkedEffectiveData_anchoredPointData_multiplicities
-- name    : HuangN13.N13MarkedEffectiveData.anchoredPointData_multiplicities
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T14:19:57.878079+00:00
-- url     : https://prove2.me/theorems/5910230d-759f-4d7f-9aa9-d07de99c2192
-- title:
--   anchoredPointData multiplicities
-- statement:
--   Exact transplant of the original proof of MazurProof.N13MarkedEffectiveData.anchoredPointData_multiplicities from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines2496–2504, command SHA-256 6c40b72a1da2340e9c92498022d334d51e59a2a8d060ab6744fc764f9f22097a.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13MarkedEffectiveData.anchoredPointData_multiplicities
    (x y : MazurProof.N13TwoChartPicardRealization.Q₂) (h : MazurProof.N13GoodModelTwo.AffineEquation x y) (b : Bool) :
    MazurProof.N13InfinityChartMarking.HasInfinityMultiplicities (MazurProof.N13EffectiveGraphData.anchoredPointData x y h b).charts
      (if b then 1 else 0) (if b then 0 else 1) := by sorry
