-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_map_mem_closedNormal
-- name    : GlobalTheory.CompanionTheory.PTIso.map_mem_closedNormal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:54:26.489905+00:00
-- url     : https://prove2.me/theorems/68555a45-9856-459b-9a82-1d34a0dad81c
-- title:
--   PTIso: map mem closed Normal
-- statement:
--   The PTIso construction uses the map mem closed Normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InertiaQuotientTransport.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InertiaQuotientTransport.lean#L11-L25

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

theorem GlobalTheory.CompanionTheory.PTIso.map_mem_closedNormal {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (Φ : A ≃ₜ* B) (X : Set A) (Y : Set B)
    (h : ∀ a ∈ X, Φ a ∈ Y) {a : A} (ha : a ∈ (Subgroup.normalClosure X).topologicalClosure) :
    Φ a ∈ (Subgroup.normalClosure Y).topologicalClosure := by sorry
