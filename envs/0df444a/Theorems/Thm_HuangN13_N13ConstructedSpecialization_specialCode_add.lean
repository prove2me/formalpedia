-- Prove2me | Theorems.Thm_HuangN13_N13ConstructedSpecialization_specialCode_add
-- name    : HuangN13.N13ConstructedSpecialization.specialCode_add
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:20:48.166117+00:00
-- url     : https://prove2.me/theorems/a58b1e0b-ff95-45ea-889c-0f57c393bde6
-- title:
--   specialCode add
-- statement:
--   Exact transplant of the original proof of MazurProof.N13ConstructedSpecialization.specialCode_add from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines4019–4022, command SHA-256 25247864cbff1383ffb35920a42d07d639c8d3d0b03db1d27555e22c71395ff1.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SeparationDataCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13ConstructedSpecialization.specialCode_add (P Q : MazurProof.N13ConstructedSpecialization.G) : MazurProof.N13ConstructedSpecialization.specialCode (P + Q) = MazurProof.N13ConstructedSpecialization.specialCode P + MazurProof.N13ConstructedSpecialization.specialCode Q := by sorry
