-- Prove2me | Theorems.Thm_GlobalTheory_T_charZero_stalk_imageOfGenericPoint
-- name    : GlobalTheory.T.charZero_stalk_imageOfGenericPoint
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:27.752094+00:00
-- url     : https://prove2.me/theorems/b36583d8-4cfb-43a5-a907-005d31b3ac00
-- title:
--   T: char Zero stalk image Of Generic Point
-- statement:
--   The T construction uses the char Zero stalk image Of Generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharZeroStalkImageOfGenericPointStatement.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharZeroStalkImageOfGenericPointStatement.lean#L9-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharZeroStalkImageOfGenericPoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharZeroStalkImageOfGenericPointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.charZero_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y], CharZero Γ(Y, ⊤) →
    ∀ (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK
    CharZero (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by sorry
