-- Prove2me | Theorems.Thm_HuangN13_N13ConstructedRationalPointTheorem_exists_separated_compatibleReduction
-- name    : HuangN13.N13ConstructedRationalPointTheorem.exists_separated_compatibleReduction
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:53:58.030491+00:00
-- url     : https://prove2.me/theorems/c4145457-967e-41e9-8703-da653c57dade
-- title:
--   Existence of a compatible reduction with separated kernel
-- statement:
--   The fixed order-thirteen rational-point problem admits a compatible reduction whose reduction kernel is separated under multiplication by two. The original constructed compatible reduction and quotient-kernel separation theorem supply this witness.
-- source:
--   Xiang Huang, Apache-2.0; FLT@51bbb4f191ad0d3753b87123635c100a638ae580. Exact witness N13ConstructedReductionClassifier.compatibleReduction (FlatLeafPacked4118–4124) and N13ConstructedRationalPointTheorem.quotient_kernel_separated (6100–6103).

import Definitions.Def_MazurN13_L4

set_option autoImplicit false

theorem HuangN13.N13ConstructedRationalPointTheorem.exists_separated_compatibleReduction : ∃ D : MazurProof.N13RationalPointEndgame.CompatibleReduction, MazurProof.N18RouteC.Separated.NSeparated D.classifier.red.ker 2 := by sorry
