-- Prove2me | Theorems.Thm_GlobalTheory_T_preimage_connectedComponent_rationalPoint_fieldExt
-- name    : GlobalTheory.T.preimage_connectedComponent_rationalPoint_fieldExt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:55:45.368079+00:00
-- url     : https://prove2.me/theorems/287339c1-b73a-4e02-86ee-ee86cfa542c0
-- title:
--   T: preimage connected Component rational Point field Ext
-- statement:
--   The T construction uses the preimage connected Component rational Point field Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreimageConnectedComponentRationalPointFieldExtStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreimageConnectedComponentRationalPointFieldExtStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageConnectedComponentRationalPointFieldExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageConnectedComponentRationalPointFieldExtStatement
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

theorem GlobalTheory.T.preimage_connectedComponent_rationalPoint_fieldExt : ∀ (k k' : Type) [Field k] [Field k'] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k')) (p : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) (q : X' ⟶ X) (e : Spec (CommRingCat.of k) ⟶ X) (e' : Spec (CommRingCat.of k') ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' connectedComponent (e (IsLocalRing.closedPoint k)) = connectedComponent (e' (IsLocalRing.closedPoint k')) := by sorry
