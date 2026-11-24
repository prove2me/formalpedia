-- Prove2me | Theorems.Thm_GlobalTheory_exists_eq_algebraMap_of_forall_ringHom_eq
-- name    : GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:44.485817+00:00
-- url     : https://prove2.me/theorems/3dcadfff-4895-4f23-91a4-e5c1de58b747
-- title:
--   Global Theory: exists eq algebra Map of forall ring Hom eq
-- statement:
--   The Global Theory construction uses the exists eq algebra Map of forall ring Hom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DescendElementOfFieldEqualizerFaithfullyFlat.lean#L114-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DescendElementOfFieldEqualizerFaithfullyFlat.lean#L114-L144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemRangeOfForallAlgHomEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DescendElementOfFieldEqualizerFaithfullyFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq : ∀ (R R₁ : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing R₁] [Algebra R R₁], Module.Finite R R₁ →
    Module.FaithfullyFlat R R₁ → ∀ s : R₁, (∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s) →
    ∃ e : R, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K), i₁ s = i₁ (algebraMap R R₁ e) := by sorry
