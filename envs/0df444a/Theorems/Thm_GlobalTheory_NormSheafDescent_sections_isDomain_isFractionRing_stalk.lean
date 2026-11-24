-- Prove2me | Theorems.Thm_GlobalTheory_NormSheafDescent_sections_isDomain_isFractionRing_stalk
-- name    : GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:43:21.010408+00:00
-- url     : https://prove2.me/theorems/4d3c97ba-d9c9-45a7-979a-3e39abaabac3
-- title:
--   Norm Sheaf Descent: sections is Domain is Fraction Ring stalk
-- statement:
--   The Norm Sheaf Descent construction uses the sections is Domain is Fraction Ring stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionsIsFractionRingStalkImageOfGenericPoint.lean#L9-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionsIsFractionRingStalkImageOfGenericPoint.lean#L9-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionsIsFractionRingStalkImageOfGenericPoint
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

theorem GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z] (U : Z.Opens), IsAffineOpen U →
    (U : Set Z) ⊆ Set.range π → ∀ h : GlobalTheory.NormSheafDescent.genPt π ∈ U,
    IsDomain Γ(Z, U) ∧ (letI := GlobalTheory.NormSheafDescent.algAK π U h
      IsFractionRing Γ(Z, U) (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by sorry
