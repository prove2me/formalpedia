-- Prove2me | Theorems.Thm_GlobalTheory_DegreeOneUniformiser_exists_irreducible_eq
-- name    : GlobalTheory.DegreeOneUniformiser.exists_irreducible_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:43:06.051089+00:00
-- url     : https://prove2.me/theorems/f2c3aaf2-cca6-42ad-afe6-e83a66d6fe1a
-- title:
--   Degree One Uniformiser: exists irreducible eq
-- statement:
--   The Degree One Uniformiser construction uses the exists irreducible eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IrreducibleOfValued.lean#L49-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IrreducibleOfValued.lean#L49-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IrreducibleOfValued
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory
open GlobalTheory.DegreeOneUniformiser
open IsDedekindDomain NumberField

theorem GlobalTheory.DegreeOneUniformiser.exists_irreducible_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (ψ : E →+* v.adicCompletion F), (∀ a : F, ψ (algebraMap F E a) = algebraMap F (v.adicCompletion F) a) → (∀ x : 𝓞 E, ψ (x : E) ∈ v.adicCompletionIntegers F) → (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ ψ ((x : E)⁻¹) ∉ v.adicCompletionIntegers F)) → ∀ ϖ : 𝓞 E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ π : v.adicCompletionIntegers F, Irreducible π ∧ (π : v.adicCompletion F) = ψ (ϖ : E) := by sorry
