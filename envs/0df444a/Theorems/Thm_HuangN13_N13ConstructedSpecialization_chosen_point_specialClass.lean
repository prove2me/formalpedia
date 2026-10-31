-- Prove2me | Theorems.Thm_HuangN13_N13ConstructedSpecialization_chosen_point_specialClass
-- name    : HuangN13.N13ConstructedSpecialization.chosen_point_specialClass
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:14:23.320635+00:00
-- url     : https://prove2.me/theorems/56c722a8-d330-487d-9e25-7619cb6674cf
-- title:
--   chosen point specialClass
-- statement:
--   Exact transplant of the original proof of MazurProof.N13ConstructedSpecialization.chosen_point_specialClass from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines4030–4042, command SHA-256 85c1bf6fab050451e838ee396e7792661d42f9bba6a0344c0e65a6cdd98a183e.

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

theorem HuangN13.N13ConstructedSpecialization.chosen_point_specialClass (P : MazurProof.N13RationalPointEndgame.RationalCurvePoint) :
    (MazurProof.N13CalibratedChooser.choose (MazurProof.N13RationalPointEndgame.rationalAbel P)).toSpecialPic =
      MazurProof.N13RationalPointEndgame.specialPointClass (MazurProof.N13ProperCurveReduction.reduceCurve P) := by sorry
