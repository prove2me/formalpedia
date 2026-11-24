-- Prove2me | Theorems.Thm_GlobalTheory_mul_mem_identityComponent_of_rational
-- name    : GlobalTheory.mul_mem_identityComponent_of_rational
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:11:45.432619+00:00
-- url     : https://prove2.me/theorems/9b7d99d4-d5a5-4d9f-8348-f75ff4848e9d
-- title:
--   Global Theory: mul mem identity Component of rational
-- statement:
--   The Global Theory construction uses the mul mem identity Component of rational property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulMemIdentityComponentOfRational.lean#L5-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulMemIdentityComponentOfRational.lean#L5-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulMemIdentityComponentOfRational
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

theorem GlobalTheory.mul_mem_identityComponent_of_rational : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), x.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → (x * y).left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) := by sorry
