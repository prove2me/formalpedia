-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_subgroupIso_coe
-- name    : GlobalTheory.CompanionTheory.PTIso.subgroupIso_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:19.79189+00:00
-- url     : https://prove2.me/theorems/e6ea95ce-b365-4b30-9047-3f3978a43f0c
-- title:
--   PTIso: subgroup Iso coe
-- statement:
--   The PTIso construction uses the subgroup Iso coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NineTermExactIff.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NineTermExactIff.lean#L94-L96

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PTIso

theorem GlobalTheory.CompanionTheory.PTIso.subgroupIso_coe {A B : Type} [Group A] [TopologicalSpace A] [Group B]
    [TopologicalSpace B] (Φ : A ≃ₜ* B) (H : Subgroup A) (K : Subgroup B)
    (h : ∀ a, a ∈ H ↔ Φ a ∈ K) (a : H) : ((subgroupIso Φ H K h a : K) : B) = Φ a := by sorry

attribute [defeq] GlobalTheory.CompanionTheory.PTIso.subgroupIso_coe
