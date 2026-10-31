-- Prove2me | Theorems.Thm_HuangN13_N13CalibratedChooser_choose_generic
-- name    : HuangN13.N13CalibratedChooser.choose_generic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:00:28.817031+00:00
-- url     : https://prove2.me/theorems/f44e3997-f62d-4f1a-9d93-314441a96a5b
-- title:
--   choose generic
-- statement:
--   Exact transplant of the original proof of MazurProof.N13CalibratedChooser.choose_generic from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines4162–4171, command SHA-256 cc71d2fc95962269951d65a8deeb186bc76c06538c3ea1dc675c200a5e02da4a.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13CalibratedChooser.choose_generic (P : MazurProof.N13EffectiveDataCompatibility.G) :
    (MazurProof.N13CalibratedChooser.choose P).toGenericPic = MazurProof.N13InfinityBaseChange.picMapRatToQ₂ P := by sorry
