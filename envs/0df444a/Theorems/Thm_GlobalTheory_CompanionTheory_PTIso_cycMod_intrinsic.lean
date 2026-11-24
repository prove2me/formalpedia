-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_cycMod_intrinsic
-- name    : GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:54:51.280983+00:00
-- url     : https://prove2.me/theorems/a5b714af-9dc1-468e-aca5-ce740ac0f109
-- title:
--   PTIso: cyc Mod intrinsic
-- statement:
--   The PTIso construction uses the cyc Mod intrinsic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RingEquivCyclotomicCharacter.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RingEquivCyclotomicCharacter.lean#L19-L31

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RingEquivCyclotomicCharacter
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

theorem GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω), cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ := by sorry
