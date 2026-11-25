-- Prove2me | Theorems.Thm_GlobalTheory_stableUnderGeneralization_sectionComponents
-- name    : GlobalTheory.stableUnderGeneralization_sectionComponents
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:39.777718+00:00
-- url     : https://prove2.me/theorems/d22c0fee-5bbb-494e-acf3-e70c8f9960f5
-- title:
--   Global Theory: stable Under Generalization section Components
-- statement:
--   The Global Theory construction uses the stable Under Generalization section Components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableUnderGeneralizationSectionComponents.lean#L10-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StableUnderGeneralizationSectionComponents.lean#L10-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsValuationRingDominatingSpecializationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionMemComponentGenericOfClosedValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableUnderGeneralizationSectionComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.stableUnderGeneralization_sectionComponents :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ →
      StableUnderGeneralization {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by sorry
