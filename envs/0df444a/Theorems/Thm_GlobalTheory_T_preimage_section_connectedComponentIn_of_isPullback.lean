-- Prove2me | Theorems.Thm_GlobalTheory_T_preimage_section_connectedComponentIn_of_isPullback
-- name    : GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:07.557+00:00
-- url     : https://prove2.me/theorems/6c08b760-b879-4081-8f33-e11023f64622
-- title:
--   T: preimage section connected Component In of is Pullback
-- statement:
--   The T construction uses the preimage section connected Component In of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionComponentsPreimageOfIsPullbackStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SectionComponentsPreimageOfIsPullbackStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullbackStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback : ∀ (X S X' S' : Scheme.{0}) (f : X ⟶ S) (f' : X' ⟶ S') (p : S' ⟶ S) (q : X' ⟶ X) (e : S ⟶ X) (e' : S' ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} = {x : X' | x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (e' (f' x))} := by sorry
