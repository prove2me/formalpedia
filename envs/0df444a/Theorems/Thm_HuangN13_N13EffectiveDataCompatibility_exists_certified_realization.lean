-- Prove2me | Theorems.Thm_HuangN13_N13EffectiveDataCompatibility_exists_certified_realization
-- name    : HuangN13.N13EffectiveDataCompatibility.exists_certified_realization
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T15:26:59.679748+00:00
-- url     : https://prove2.me/theorems/a7ef3f70-85f5-4b90-81b3-6f324bd6aa3c
-- title:
--   exists certified realization
-- statement:
--   Exact transplant of the original proof of MazurProof.N13EffectiveDataCompatibility.exists_certified_realization from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines2869–2884, command SHA-256 03ec921602d7523fad1c66a064c1907949e4ec6babb556d147e5fb73f0cec13c.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_InfinityMultiplicityCore
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_PrimitiveAffineComparisonCore

set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13InfinityBaseChange.instFactPrimeOfNatNat_fLT

theorem HuangN13.N13EffectiveDataCompatibility.exists_certified_realization (P : MazurProof.N13EffectiveDataCompatibility.G) :
    ∃ D : MazurProof.N13TwoChartPicardRealization.Data, MazurProof.N13EffectiveDataCompatibility.Certified D ∧ D.toGenericPic = MazurProof.N13InfinityBaseChange.picMapRatToQ₂ P := by sorry
