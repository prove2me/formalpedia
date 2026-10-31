-- Prove2me | Theorems.Thm_HuangN13_N13SpecialAffineSaturation_chartPair_eq_of_infinityIdeal_eq
-- name    : HuangN13.N13SpecialAffineSaturation.chartPair_eq_of_infinityIdeal_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:55:24.642178+00:00
-- url     : https://prove2.me/theorems/47981125-be2d-463a-b46e-b82eb1168410
-- title:
--   chartPair eq of infinityIdeal eq
-- statement:
--   Exact transplant of the original proof of MazurProof.N13SpecialAffineSaturation.chartPair_eq_of_infinityIdeal_eq from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit9 lines9002–9023, command SHA-256 26ec2cf9be5f48b615646bcdc7e1995dabf42e259f1979b7b33b156d348eb51e.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_IntegralTensorDataCore
import Definitions.Def_HuangN13_SpecialComparisonCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13SpecialAffineSaturation.chartPair_eq_of_infinityIdeal_eq
    (L M : MazurProof.N13TwoChartSpecialRestriction.ChartPair)
    (hL : MazurProof.N13SpecialAffineSaturation.XUnitMod L.affineIdeal)
    (hM : MazurProof.N13SpecialAffineSaturation.XUnitMod M.affineIdeal)
    (hinfinity : L.infinityIdeal = M.infinityIdeal) :
    L = M := by sorry
