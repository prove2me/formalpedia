-- Prove2me | Theorems.Thm_GlobalTheory_T_descend_element_of_field_equalizer_faithfully_flat
-- name    : GlobalTheory.T.descend_element_of_field_equalizer_faithfully_flat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:20.056841+00:00
-- url     : https://prove2.me/theorems/a7206de1-cd66-4f7e-ba9e-7d2c5cedfd8c
-- title:
--   T: descend element of field equalizer faithfully flat
-- statement:
--   The T construction uses the descend element of field equalizer faithfully flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DescendElementOfFieldEqualizerFaithfullyFlatStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DescendElementOfFieldEqualizerFaithfullyFlatStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DescendElementOfFieldEqualizerFaithfullyFlat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DescendElementOfFieldEqualizerFaithfullyFlatStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.descend_element_of_field_equalizer_faithfully_flat : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] [CommRing R₁] [Algebra R R₁], Module.Finite R R₁ → Module.FaithfullyFlat R R₁ → ∀ s : R₁, (∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s) → ∃ e : R, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K), i₁ s = i₁ (algebraMap R R₁ e) := by sorry
