-- Prove2me | Theorems.Thm_GlobalTheory_UT_ExactTerm_exists_torsion_lift
-- name    : GlobalTheory.UT.ExactTerm.exists_torsion_lift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:19:18.306936+00:00
-- url     : https://prove2.me/theorems/835bf42e-9273-45f9-83bb-d8b3c599fdcc
-- title:
--   Exact Term: exists torsion lift
-- statement:
--   The Exact Term construction uses the exists torsion lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTorsionLift.lean#L102-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTorsionLift.lean#L102-L131

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorsionLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.ExactTerm

theorem GlobalTheory.UT.ExactTerm.exists_torsion_lift {F : Type} [Field F] [IsAlgClosed F] (O : ValuationSubring F) {S : Scheme.{0}}
    (G : Over S) [GrpObj G] (n : ℕ) [IsFinite ((𝟙 G) ^ n : G ⟶ G).left] [Flat ((𝟙 G) ^ n : G ⟶ G).left]
    (t : Spec (CommRingCat.of O) ⟶ S)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (residue O)) ≫ t) ⟶ G) (hx : x ^ n = 1) :
    ∃ y : Over.mk t ⟶ G, y ^ n = 1 ∧ Spec.map (CommRingCat.ofHom (residue O)) ≫ y.left = x.left := by sorry
