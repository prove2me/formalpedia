-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFixed_coe_eK
-- name    : GlobalTheory.CompanionTheory.HeckeFixed.coe_eK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:59.472062+00:00
-- url     : https://prove2.me/theorems/a1d1f8e8-5a2c-4bf4-97b1-a9e4c91e98de
-- title:
--   Hecke Fixed: coe e K
-- statement:
--   The Hecke Fixed construction uses the coe e K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeckeCharacterExistsUnique.lean#L193-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeckeCharacterExistsUnique.lean#L193-L194

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

theorem GlobalTheory.CompanionTheory.HeckeFixed.coe_eK (v : V) : (eK π hπ hKc v : V) =
    (Submodule.projectionOnto _ _ (isCompl_res hπ hKc) v : V) := by sorry
