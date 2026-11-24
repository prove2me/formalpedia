-- Prove2me | Theorems.Thm_GlobalTheory_NormSheafDescent_charZero_stalk_genPt
-- name    : GlobalTheory.NormSheafDescent.charZero_stalk_genPt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:43:40.992501+00:00
-- url     : https://prove2.me/theorems/3c5af7cd-bac2-495b-8f90-c7908f2ba5af
-- title:
--   Norm Sheaf Descent: char Zero stalk gen Pt
-- statement:
--   The Norm Sheaf Descent construction uses the char Zero stalk gen Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharZeroStalkImageOfGenericPoint.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CharZeroStalkImageOfGenericPoint.lean#L9-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharZeroStalkImageOfGenericPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NormSheafDescent

theorem GlobalTheory.NormSheafDescent.charZero_stalk_genPt : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y], CharZero Γ(Y, ⊤) →
    ∀ (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK
    CharZero (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by sorry
