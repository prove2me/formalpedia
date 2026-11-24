-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_nineG_of_iso
-- name    : GlobalTheory.CompanionTheory.PTIso.NineTransfer.nineG_of_iso
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:54:48.378001+00:00
-- url     : https://prove2.me/theorems/c84fd296-0a6d-4310-b611-a72037179c1c
-- title:
--   Nine Transfer: nine G of iso
-- statement:
--   The Nine Transfer construction uses the nine G of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateSequenceTransport.lean#L224-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateSequenceTransport.lean#L224-L261

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateSequenceTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso GlobalTheory.CompanionTheory.PTIso.NineTransfer

theorem GlobalTheory.CompanionTheory.PTIso.NineTransfer.nineG_of_iso {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type}
    [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)]
    [∀ i, TopologicalSpace (D i)] [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
    (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ')
    (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) {M : Type} [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M)
    (ρ' : Representation R Γ' M) (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i)) :
    (∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) → (∀ g, χ' (eG g) = χ g) →
    (∀ g m, ρ' (eG g) m = ρ g m) →
    ∀ (j : ∀ i, H2 ((charRep χ).comp (φ i)) →ₗ[R] R)
      (j' : ∀ i, H2 ((charRep χ').comp (φ' i)) →ₗ[R] R)
      (hρ : ContAction ρ) (hρ' : ContAction ρ'),
      (∀ (i : I) (z : Z2 ((charRep χ).comp (φ i))) (z' : Z2 ((charRep χ').comp (φ' (eI i)))),
        (∀ g h, z'.1 (eD i g, eD i h) = z.1 (g, h)) →
          j' (eI i) (Submodule.Quotient.mk z') = j i (Submodule.Quotient.mk z)) →
      NineG φ' hφ' χ' j' ρ' hρ' → NineG φ hφ χ j ρ hρ := by sorry
