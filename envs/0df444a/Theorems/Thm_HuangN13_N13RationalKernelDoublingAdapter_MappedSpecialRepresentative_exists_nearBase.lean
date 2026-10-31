-- Prove2me | Theorems.Thm_HuangN13_N13RationalKernelDoublingAdapter_MappedSpecialRepresentative_exists_nearBase
-- name    : HuangN13.N13RationalKernelDoublingAdapter.MappedSpecialRepresentative.exists_nearBase
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:30:59.980301+00:00
-- url     : https://prove2.me/theorems/8eb37cd0-a677-458a-a9fe-7ffed688b9d7
-- title:
--   exists nearBase
-- statement:
--   Exact transplant of the original proof of MazurProof.N13RationalKernelDoublingAdapter.MappedSpecialRepresentative.exists_nearBase from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit19 lines6987–7006, command SHA-256 79cfbfdb3dd2b17492909cc4f7fda7aafb14e5480a187c4867eaa8dc418d7a04.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13RationalKernelDoublingAdapter.MappedSpecialRepresentative.exists_nearBase {c : MazurProof.N13RationalKernelDoublingAdapter.Pic₂}
    (R : MazurProof.N13RationalKernelDoublingAdapter.MappedSpecialRepresentative c) :
    ∃ E : MazurProof.N13RationalKernelDoublingAdapter.NearBaseMumford, E.centeredPic = c := by sorry
