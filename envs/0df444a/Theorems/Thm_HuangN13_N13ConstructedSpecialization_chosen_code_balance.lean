-- Prove2me | Theorems.Thm_HuangN13_N13ConstructedSpecialization_chosen_code_balance
-- name    : HuangN13.N13ConstructedSpecialization.chosen_code_balance
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:14:56.493618+00:00
-- url     : https://prove2.me/theorems/d2488cb0-9596-4259-b921-441cf3818d74
-- title:
--   chosen code balance
-- statement:
--   Exact transplant of the original proof of MazurProof.N13ConstructedSpecialization.chosen_code_balance from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines4006–4013, command SHA-256 d6dc266d769440f4999d4bfebef75ace8d4bbf94d22bccb05bad05ff93b5d5f9.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13ConstructedSpecialization.chosen_code_balance (P Q : MazurProof.N13ConstructedSpecialization.G) :
    MazurProof.N13SpecialAbelCode.divisorCode (MazurProof.N13ConstructedSpecialization.chosenDivisor P) + MazurProof.N13SpecialAbelCode.divisorCode (MazurProof.N13ConstructedSpecialization.chosenDivisor Q) =
      MazurProof.N13SpecialAbelCode.divisorCode (MazurProof.N13ConstructedSpecialization.chosenDivisor (P + Q)) + MazurProof.N13SpecialAbelCode.divisorCode (MazurProof.N13ConstructedSpecialization.chosenDivisor 0) := by sorry
