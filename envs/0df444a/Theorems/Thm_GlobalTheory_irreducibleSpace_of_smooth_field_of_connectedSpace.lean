-- Prove2me | Theorems.Thm_GlobalTheory_irreducibleSpace_of_smooth_field_of_connectedSpace
-- name    : GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:42:11.883113+00:00
-- url     : https://prove2.me/theorems/b337a7a4-15a3-4b7e-880b-84153de93c95
-- title:
--   Global Theory: irreducible Space of smooth field of connected Space
-- statement:
--   The Global Theory construction uses the irreducible Space of smooth field of connected Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpaceOfSmoothFieldOfConnectedSpace.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpaceOfSmoothFieldOfConnectedSpace.lean#L12-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothFieldOfConnectedSpace
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)), Smooth f →
      ConnectedSpace X → IrreducibleSpace X := by sorry
