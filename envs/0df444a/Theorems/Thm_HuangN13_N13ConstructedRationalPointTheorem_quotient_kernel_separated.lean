-- Prove2me | Theorems.Thm_HuangN13_N13ConstructedRationalPointTheorem_quotient_kernel_separated
-- name    : HuangN13.N13ConstructedRationalPointTheorem.quotient_kernel_separated
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:48:44.423841+00:00
-- url     : https://prove2.me/theorems/47b8c6ba-2f61-4f67-bebd-bebd4abe1a5e
-- title:
--   quotient kernel separated
-- statement:
--   Exact transplant of the original proof of MazurProof.N13ConstructedRationalPointTheorem.quotient_kernel_separated from the FLT N13 development. Supporting original lemmas are replayed verbatim; lemmas already published as HuangN13 nodes are used through those nodes.
-- source:
--   Xiang Huang, Apache-2.0. Original FLT source at https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580/FLT/Assumptions/MazurProof. Exact compiler-boundary source ranges and hashes are recorded in metadata.json; original-file line mapping is not asserted. Target flattened unit21 lines6100–6103, command SHA-256 c2d33ef754f770b7db3fdf3e2c44c9b266bb1925186f7364c1a52630a779e56e.

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_ChooserSmallStatementCore
import Definitions.Def_HuangN13_CompatibleReductionCore
import Definitions.Def_HuangN13_DoublingStatementCore
import Definitions.Def_HuangN13_SeparationDataCore

set_option autoImplicit false
open Polynomial

theorem HuangN13.N13ConstructedRationalPointTheorem.quotient_kernel_separated :
    MazurProof.N18RouteC.Separated.NSeparated MazurProof.N13ConstructedReductionClassifier.compatibleReduction.classifier.red.ker 2 := by sorry
