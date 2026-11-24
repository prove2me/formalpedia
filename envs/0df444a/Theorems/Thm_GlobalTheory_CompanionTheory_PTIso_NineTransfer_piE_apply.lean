-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_NineTransfer_piE_apply
-- name    : GlobalTheory.CompanionTheory.PTIso.NineTransfer.piE_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:19.596411+00:00
-- url     : https://prove2.me/theorems/65001582-0ada-4461-a23d-14ed0ae6f35e
-- title:
--   Nine Transfer: pi E apply
-- statement:
--   The Nine Transfer construction uses the pi E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateSequenceTransport.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateSequenceTransport.lean#L88-L91

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
variable {R : Type*} [CommRing R]

theorem GlobalTheory.CompanionTheory.PTIso.NineTransfer.piE_apply {I I' : Type*} {A : I' → Type*} {B : I → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module R (B i)] (eI : I ≃ I') (e : ∀ i, A (eI i) ≃ₗ[R] B i) (x : ∀ i', A i') (i : I) :
    piE eI e x i = e i (x (eI i)) := by sorry

attribute [defeq] GlobalTheory.CompanionTheory.PTIso.NineTransfer.piE_apply
