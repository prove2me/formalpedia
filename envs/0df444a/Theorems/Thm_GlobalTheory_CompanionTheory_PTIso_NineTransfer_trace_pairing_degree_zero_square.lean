-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_trace_pairing_degree_zero_square
-- name    : GlobalTheory.CompanionTheory.PTIso.NineTransfer.trace_pairing_degree_zero_square
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:54:52.811809+00:00
-- url     : https://prove2.me/theorems/78687d78-2340-4a81-aa27-1e5d18b69dc1
-- title:
--   Nine Transfer: trace pairing degree zero square
-- statement:
--   The Nine Transfer construction uses the trace pairing degree zero square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateSequenceTransport.lean#L172-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateSequenceTransport.lean#L172-L184

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
variable (j : ∀ i, H2 ((charRep χ).comp (φ i)) →ₗ[R] R)
  (j' : ∀ i, H2 ((charRep χ').comp (φ' i)) →ₗ[R] R)
  (hj : ∀ (i : I) (z : Z2 ((charRep χ).comp (φ i))) (z' : Z2 ((charRep χ').comp (φ' (eI i)))),
    (∀ g h, z'.1 (eD i g, eD i h) = z.1 (g, h)) →
      j' (eI i) (Submodule.Quotient.mk z') = j i (Submodule.Quotient.mk z))
include hD hj

theorem GlobalTheory.CompanionTheory.PTIso.NineTransfer.trace_pairing_degree_zero_square (x : ∀ i', H0 (ρ'.comp (φ' i'))) (y : H2 (twDual χ' ρ')) :
    gtr0 φ hφ χ j ρ (P0 φ φ' ρ ρ' eI eD hl x) (equivH2OfIso eG _ _ hd y) =
      gtr0 φ' hφ' χ' j' ρ' x y := by sorry
