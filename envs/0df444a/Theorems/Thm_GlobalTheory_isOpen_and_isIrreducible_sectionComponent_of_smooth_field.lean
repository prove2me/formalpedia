-- Prove2me | Theorems.Thm_GlobalTheory_isOpen_and_isIrreducible_sectionComponent_of_smooth_field
-- name    : GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:15.906799+00:00
-- url     : https://prove2.me/theorems/a807bd8d-e375-4459-b3b9-1453fbce0657
-- title:
--   Global Theory: is Open and is Irreducible section Component of smooth field
-- statement:
--   The Global Theory construction uses the is Open and is Irreducible section Component of smooth field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenIsIrreducibleComponentOfRationalPointSmoot.lean#L10-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenIsIrreducibleComponentOfRationalPointSmoot.lean#L10-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothFieldOfConnectedSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIsIrreducibleComponentOfRationalPointSmoot
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

theorem GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field
    (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    (e : Spec (CommRingCat.of k) ⟶ X) (hf : Smooth f) (he : e ≫ f = 𝟙 _) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧
      IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by sorry
