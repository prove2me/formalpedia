-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_local_degree_two_square
-- name    : GlobalTheory.CompanionTheory.PTIso.NineTransfer.local_degree_two_square
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:54:21.499514+00:00
-- url     : https://prove2.me/theorems/6c691b4b-a3d8-46a4-811d-8665a930b1ee
-- title:
--   Nine Transfer: local degree two square
-- statement:
--   The Nine Transfer construction uses the local degree two square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateSequenceTransport.lean#L153-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateSequenceTransport.lean#L153-L163

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
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {Γ Γ' : Type}
  [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type} [Fintype I]
  [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ')
  (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ)
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
  (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i))
  (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) (hχ : ∀ g, χ' (eG g) = χ g)
  (hc : ∀ g m, ρ' (eG g) m = ρ g m)
  (hd : ∀ g f, twDual χ' ρ' (eG g) f = twDual χ ρ g f)
  (hl : ∀ i d m, (ρ'.comp (φ' (eI i))) (eD i d) m = (ρ.comp (φ i)) d m)
include hD

theorem GlobalTheory.CompanionTheory.PTIso.NineTransfer.local_degree_two_square (x : H2 ρ') :
    gloc2 φ hφ ρ (equivH2OfIso eG ρ' ρ hc x) = P2 φ φ' ρ ρ' eI eD hl (gloc2 φ' hφ' ρ' x) := by sorry
