-- Prove2me | Theorems.Thm_GlobalTheory_EtaleFibre_encard_points_eq_finrank
-- name    : GlobalTheory.EtaleFibre.encard_points_eq_finrank
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:46.634067+00:00
-- url     : https://prove2.me/theorems/6bda9a87-2ac7-5c9b-8722-740ac0b2347f
-- title:
--   Etale Fibre: encard points eq finrank
-- statement:
--   The Etale Fibre construction uses the encard points eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtaleFibreEmbeddingsCard.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtaleFibreEmbeddingsCard.lean#L28-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleFibreEmbeddingsCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.EtaleFibre

theorem GlobalTheory.EtaleFibre.encard_points_eq_finrank : ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] (f : A →+* B), f.Finite → f.Etale → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (letI := f.toAlgebra; Module.finrank A B : ℕ) := by sorry
