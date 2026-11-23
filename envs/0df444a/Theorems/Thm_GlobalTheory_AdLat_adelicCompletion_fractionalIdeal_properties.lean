-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_adelicCompletion_fractionalIdeal_properties
-- name    : GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:10:39.216087+00:00
-- url     : https://prove2.me/theorems/d244b9f0-fba4-48b5-aa31-cb51df8ee6d5
-- title:
--   Ad Lat: adelic Completion fractional Ideal properties
-- statement:
--   The Ad Lat construction uses the adelic Completion fractional Ideal properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealProperties.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealProperties.lean#L154-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat

theorem GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ I J : FractionalIdeal (𝓞 E)⁰ E, ∀ x ∈ hat1 F (I : Set E), ∀ y ∈ hat1 F (J : Set E), x * y ∈ hat1 F ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ (∀ (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I) ∧ (∀ (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E), I ≠ 0 → (∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) → z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ ∀ (c : E ≃ₐ[F] E) (I I' : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, c x ∈ I') → ∀ z ∈ hat1 F (I : Set E), sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F (I' : Set E) := by sorry
