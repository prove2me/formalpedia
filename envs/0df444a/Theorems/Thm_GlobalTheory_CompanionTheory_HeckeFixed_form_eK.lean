-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFixed_form_eK
-- name    : GlobalTheory.CompanionTheory.HeckeFixed.form_eK
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:34.424798+00:00
-- url     : https://prove2.me/theorems/7fba92f1-317d-4d2e-b979-d2ed454a7f8d
-- title:
--   Hecke Fixed: form e K
-- statement:
--   The Hecke Fixed construction uses the form e K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeckeCharacterExistsUnique.lean#L209-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeckeCharacterExistsUnique.lean#L209-L222

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_LocalBaseChange_TwistedIndependenceLemma_TwistedIndependence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeCharacterExistsUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeFixed
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
variable {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G}
  (hKc : IsCompact (K : Set G))

theorem GlobalTheory.CompanionTheory.HeckeFixed.form_eK (l : Module.Dual ℂ V) (hl : ∀ x ∈ K, l ∘ₗ π x = l) (v : V) :
    l (eK π hπ hKc v : V) = l v := by sorry
