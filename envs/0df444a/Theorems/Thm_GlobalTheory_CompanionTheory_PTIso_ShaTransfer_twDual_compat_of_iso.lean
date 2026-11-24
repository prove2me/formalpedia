-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_ShaTransfer_twDual_compat_of_iso
-- name    : GlobalTheory.CompanionTheory.PTIso.ShaTransfer.twDual_compat_of_iso
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:54:30.502907+00:00
-- url     : https://prove2.me/theorems/980ec8d8-9826-469e-b149-e978d576d321
-- title:
--   Sha Transfer: tw Dual compat of iso
-- statement:
--   The Sha Transfer construction uses the tw Dual compat of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TateShafarevichTransport.lean#L123-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TateShafarevichTransport.lean#L123-L130

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TateShafarevichTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.ShaTransfer

theorem GlobalTheory.CompanionTheory.PTIso.ShaTransfer.twDual_compat_of_iso {R Γ Γ' M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [Group Γ'] [TopologicalSpace Γ'] [AddCommGroup M] [Module R M]
    (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (eG : Γ ≃ₜ* Γ') (hχ : ∀ g, χ' (eG g) = χ g) (hρ : ∀ g m, ρ' (eG g) m = ρ g m) :
    ∀ g ψ, twDual χ' ρ' (eG g) ψ = twDual χ ρ g ψ := by sorry
