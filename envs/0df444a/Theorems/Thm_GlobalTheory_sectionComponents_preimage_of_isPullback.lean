-- Prove2me | Theorems.Thm_GlobalTheory_sectionComponents_preimage_of_isPullback
-- name    : GlobalTheory.sectionComponents_preimage_of_isPullback
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:20:58.875961+00:00
-- url     : https://prove2.me/theorems/29e8f913-18a1-4b85-b7c6-5c6e1d8e0c40
-- title:
--   Global Theory: section Components preimage of is Pullback
-- statement:
--   The Global Theory construction uses the section Components preimage of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionComponentsPreimageOfIsPullback.lean#L10-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionComponentsPreimageOfIsPullback.lean#L10-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageConnectedComponentRationalPointFieldExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComponentInFibreIffOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullback
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

theorem GlobalTheory.sectionComponents_preimage_of_isPullback :
    ∀ (X S X' S' : Scheme.{0}) (f : X ⟶ S) (f' : X' ⟶ S') (p : S' ⟶ S) (q : X' ⟶ X)
      (e : S ⟶ X) (e' : S' ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ →
      e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e →
      q ⁻¹' {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} =
        {x : X' | x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (e' (f' x))} := by sorry
