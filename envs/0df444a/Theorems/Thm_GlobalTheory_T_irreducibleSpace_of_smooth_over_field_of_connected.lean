-- Prove2me | Theorems.Thm_GlobalTheory_T_irreducibleSpace_of_smooth_over_field_of_connected
-- name    : GlobalTheory.T.irreducibleSpace_of_smooth_over_field_of_connected
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:46:50.148081+00:00
-- url     : https://prove2.me/theorems/3d060d4e-2b0b-4ad6-b6ba-541a60182539
-- title:
--   T: irreducible Space of smooth over field of connected
-- statement:
--   The T construction uses the irreducible Space of smooth over field of connected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpaceOfSmoothFieldOfConnectedSpaceStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrreducibleSpaceOfSmoothFieldOfConnectedSpaceStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleSpaceOfSmoothFieldOfConnectedSpaceStatement
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

theorem GlobalTheory.T.irreducibleSpace_of_smooth_over_field_of_connected : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)), Smooth f → ConnectedSpace X → IrreducibleSpace X := by sorry
