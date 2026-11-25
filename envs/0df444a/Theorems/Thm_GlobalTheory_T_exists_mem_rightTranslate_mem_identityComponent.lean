-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_mem_rightTranslate_mem_identityComponent
-- name    : GlobalTheory.T.exists_mem_rightTranslate_mem_identityComponent
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:07:51.235786+00:00
-- url     : https://prove2.me/theorems/e9c13e33-f3ca-4b97-9e99-562a4c76034b
-- title:
--   T: exists mem right Translate mem identity Component
-- statement:
--   The T construction uses the exists mem right Translate mem identity Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMemRightTranslateMemIdentityComponentStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMemRightTranslateMemIdentityComponentStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMemRightTranslateMemIdentityComponent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMemRightTranslateMemIdentityComponentStatement
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

theorem GlobalTheory.T.exists_mem_rightTranslate_mem_identityComponent : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), (η[G]).left (IsLocalRing.closedPoint k) ∈ U → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → ∃ z : G.left, z ∈ U ∧ (𝟙 G * (toUnit G ≫ y) : G ⟶ G).left z ∈ U := by sorry
