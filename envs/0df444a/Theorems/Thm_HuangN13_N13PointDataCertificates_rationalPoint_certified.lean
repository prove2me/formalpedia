-- Prove2me | Theorems.Thm_HuangN13_N13PointDataCertificates_rationalPoint_certified
-- name    : HuangN13.N13PointDataCertificates.rationalPoint_certified
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:00:34.472187+00:00
-- url     : https://prove2.me/theorems/67befd08-bca6-4353-988d-337139ca6351
-- title:
--   rationalPoint certified
-- statement:
--   Exact transplant of the original proof of MazurProof.N13PointDataCertificates.rationalPoint_certified from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines3913–3935, command SHA-256 b7e4b12897806d8183551d3da632957c37b93b51da90816e539444d083ffbadb.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_FiniteInfinityClosureCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13PointDataCertificates.rationalPoint_certified (P : MazurProof.N13RationalPointEndgame.RationalCurvePoint) :
    MazurProof.N13EffectiveDataCompatibility.Certified (MazurProof.N13RationalCurvePointPicardRealization.data P).realization := by sorry
