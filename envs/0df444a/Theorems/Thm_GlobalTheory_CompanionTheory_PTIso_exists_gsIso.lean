-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_exists_gsIso
-- name    : GlobalTheory.CompanionTheory.PTIso.exists_gsIso
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:12.59902+00:00
-- url     : https://prove2.me/theorems/1a5a7485-0850-4e4a-8d42-0572dbf379f3
-- title:
--   PTIso: exists gs Iso
-- statement:
--   The PTIso construction uses the exists gs Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InertiaQuotientTransport.lean#L45-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InertiaQuotientTransport.lean#L45-L75

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InertiaQuotientTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso

theorem GlobalTheory.CompanionTheory.PTIso.exists_gsIso : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') → ∀ (T : Set (HeightOneSpectrum (𝓞 F))) (T' : Set (HeightOneSpectrum (𝓞 F'))), (∀ v, v ∈ T ↔ eV v ∈ T') → ∃ Ψ : GS Ω T ≃ₜ* GS Ω' T', ∀ σ : G F Ω, Ψ (toGS Ω T σ) = toGS Ω' T' (Φ σ) := by sorry
