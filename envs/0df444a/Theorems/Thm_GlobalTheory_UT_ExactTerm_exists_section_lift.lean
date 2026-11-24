-- Prove2me | Theorems.Thm_GlobalTheory_UT_ExactTerm_exists_section_lift
-- name    : GlobalTheory.UT.ExactTerm.exists_section_lift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:19:34.479313+00:00
-- url     : https://prove2.me/theorems/d3e290ee-c3fd-4222-8a41-ee55eaa8c017
-- title:
--   Exact Term: exists section lift
-- statement:
--   The Exact Term construction uses the exists section lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTorsionLift.lean#L72-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTorsionLift.lean#L72-L100

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

theorem GlobalTheory.UT.ExactTerm.exists_section_lift {F : Type} [Field F] [IsAlgClosed F] (O : ValuationSubring F) {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of O)) [IsFinite f] [Flat f] (p : Spec (CommRingCat.of (ResidueField O)) ⟶ H)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (residue O))) :
    ∃ q : Spec (CommRingCat.of O) ⟶ H, q ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue O)) ≫ q = p := by sorry
