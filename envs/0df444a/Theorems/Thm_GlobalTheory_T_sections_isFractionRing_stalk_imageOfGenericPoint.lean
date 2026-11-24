-- Prove2me | Theorems.Thm_GlobalTheory_T_sections_isFractionRing_stalk_imageOfGenericPoint
-- name    : GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:57:32.297848+00:00
-- url     : https://prove2.me/theorems/e003c72c-de1b-45f1-b756-4125715573a1
-- title:
--   T: sections is Fraction Ring stalk image Of Generic Point
-- statement:
--   The T construction uses the sections is Fraction Ring stalk image Of Generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionsIsFractionRingStalkImageOfGenericPointStatement.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionsIsFractionRingStalkImageOfGenericPointStatement.lean#L9-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionsIsFractionRingStalkImageOfGenericPoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionsIsFractionRingStalkImageOfGenericPointStatement
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

theorem GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z] (U : Z.Opens), IsAffineOpen U →
    (U : Set Z) ⊆ Set.range π → ∀ h : GlobalTheory.NormSheafDescent.genPt π ∈ U,
    IsDomain Γ(Z, U) ∧ (letI := GlobalTheory.NormSheafDescent.algAK π U h
      IsFractionRing Γ(Z, U) (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by sorry
