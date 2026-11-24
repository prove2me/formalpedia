-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFixed_eK_apply_of_mem_coK
-- name    : GlobalTheory.CompanionTheory.HeckeFixed.eK_apply_of_mem_coK
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:32.851803+00:00
-- url     : https://prove2.me/theorems/af93d04b-63ea-4be7-b3e0-155cfafe7a0c
-- title:
--   Hecke Fixed: e K apply of mem co K
-- statement:
--   The Hecke Fixed construction uses the e K apply of mem co K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeckeCharacterExistsUnique.lean#L200-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeckeCharacterExistsUnique.lean#L200-L203

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

theorem GlobalTheory.CompanionTheory.HeckeFixed.eK_apply_of_mem_coK {v : V} (hv : v ∈ coK (resK π K)) : eK π hπ hKc v = 0 := by sorry
