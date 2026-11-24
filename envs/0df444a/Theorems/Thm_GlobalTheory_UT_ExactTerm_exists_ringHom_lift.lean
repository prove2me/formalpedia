-- Prove2me | Theorems.Thm_GlobalTheory_UT_ExactTerm_exists_ringHom_lift
-- name    : GlobalTheory.UT.ExactTerm.exists_ringHom_lift
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:55:18.629608+00:00
-- url     : https://prove2.me/theorems/97904fdf-8a2d-4472-b04c-85925c38449b
-- title:
--   Exact Term: exists ring Hom lift
-- statement:
--   The Exact Term construction uses the exists ring Hom lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTorsionLift.lean#L9-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTorsionLift.lean#L9-L70

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

theorem GlobalTheory.UT.ExactTerm.exists_ringHom_lift (F : Type) [Field F] [IsAlgClosed F] {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O]
    [IsIntegrallyClosed O] [Algebra O F] [IsFractionRing O F] {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] (φ : A →+* ResidueField O)
    (hφ : φ.comp (algebraMap O A) = residue O) :
    ∃ ψ : A →+* O, ψ.comp (algebraMap O A) = RingHom.id O ∧ (residue O).comp ψ = φ := by sorry
