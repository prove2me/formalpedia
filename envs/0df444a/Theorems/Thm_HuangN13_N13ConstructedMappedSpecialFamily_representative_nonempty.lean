-- Prove2me | Theorems.Thm_HuangN13_N13ConstructedMappedSpecialFamily_representative_nonempty
-- name    : HuangN13.N13ConstructedMappedSpecialFamily.representative_nonempty
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:39:33.290497+00:00
-- url     : https://prove2.me/theorems/b6b0281c-221c-44fd-89f6-f9a48041d9b3
-- title:
--   representative nonempty
-- statement:
--   Exact transplant of the original proof of MazurProof.N13ConstructedMappedSpecialFamily.representative_nonempty from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines4692–4711, command SHA-256 d6d2f099914371985d66be3e09748c69e017ee06fe403906c41f10c09ac73b65.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_CompatibleReductionCore
import Definitions.Def_HuangN13_DoublingStatementCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13ConstructedMappedSpecialFamily.representative_nonempty (z : MazurProof.N13KernelBaseDivisor.Kernel) :
    Nonempty (MazurProof.N13RationalKernelDoublingAdapter.MappedSpecialRepresentative
      (MazurProof.N13TwoAdicAbelChartSection.subgroupToPic MazurProof.N13KernelBaseDivisor.Kernel z)) := by sorry
