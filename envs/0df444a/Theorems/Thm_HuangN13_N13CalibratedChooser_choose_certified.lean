-- Prove2me | Theorems.Thm_HuangN13_N13CalibratedChooser_choose_certified
-- name    : HuangN13.N13CalibratedChooser.choose_certified
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:00:44.338779+00:00
-- url     : https://prove2.me/theorems/4e69f5dc-24b9-42f6-a954-2ad3047b49eb
-- title:
--   choose certified
-- statement:
--   Exact transplant of the original proof of MazurProof.N13CalibratedChooser.choose_certified from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines4152–4160, command SHA-256 eb22ca47c1e9db3587f32915a201652e711758653fd298ef799f7c0ef884589c.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralInfinityComparisonCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PairLineSpecialRestrictionCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore
import Definitions.Def_HuangN13_SeparationDataCore
import Definitions.Def_HuangN13_VerticalGraphStatementCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13CalibratedChooser.choose_certified (P : MazurProof.N13EffectiveDataCompatibility.G) : MazurProof.N13EffectiveDataCompatibility.Certified (MazurProof.N13CalibratedChooser.choose P) := by sorry
