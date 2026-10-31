-- Prove2me | Theorems.Thm_HuangN13_N13IntegralInfinityVerticalGraphSpecialRestriction_constantInfinityFibre_affine_xUnitMod
-- name    : HuangN13.N13IntegralInfinityVerticalGraphSpecialRestriction.constantInfinityFibre_affine_xUnitMod
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T12:55:26.742692+00:00
-- url     : https://prove2.me/theorems/1d67c466-a0d8-4f87-9df2-6365dc7faceb
-- title:
--   constantInfinityFibre affine xUnitMod
-- statement:
--   Exact transplant of the original proof of MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.constantInfinityFibre_affine_xUnitMod from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit9 lines10457–10486, command SHA-256 94d4c642109a6825be6f68c0d7631b84955a07b5a4cb151b527ec7681e955140.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SpecialComparisonCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13IntegralInfinityVerticalGraphSpecialRestriction.constantInfinityFibre_affine_xUnitMod
    (a : MazurProof.N13IntegralInfinityVerticalGraphSpecialRestriction.K) :
    MazurProof.N13SpecialAffineSaturation.XUnitMod
      (MazurProof.N13SpecialDivisorCharts.ofDivisor
        (MazurProof.N13SpecialVerticalDivisorCharts.constantInfinityFibreDivisor
          a)).affineIdeal := by sorry
