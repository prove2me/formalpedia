-- Prove2me | Theorems.Thm_GlobalTheory_T_isField_stalk_imageOfGenericPoint
-- name    : GlobalTheory.T.isField_stalk_imageOfGenericPoint
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:06.726324+00:00
-- url     : https://prove2.me/theorems/e9c61251-161a-5236-ad60-19b6298ab72b
-- title:
--   T: is Field stalk image Of Generic Point
-- statement:
--   The T construction uses the is Field stalk image Of Generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFieldStalkImageOfGenericPointStatement.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFieldStalkImageOfGenericPointStatement.lean#L9-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFieldStalkImageOfGenericPoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFieldStalkImageOfGenericPointStatement
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

theorem GlobalTheory.T.isField_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z], IsOpen (Set.range π) →
    IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by sorry
