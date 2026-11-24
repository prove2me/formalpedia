-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFixed_IsHeckeOn_unique
-- name    : GlobalTheory.CompanionTheory.HeckeFixed.IsHeckeOn.unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:02.56922+00:00
-- url     : https://prove2.me/theorems/1e156129-c3f1-4578-81b1-36368fddcee4
-- title:
--   Is Hecke On: unique
-- statement:
--   The Is Hecke On construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeckeCharacterExistsUnique.lean#L236-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeckeCharacterExistsUnique.lean#L236-L249

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
include hπ hKc

theorem GlobalTheory.CompanionTheory.HeckeFixed.IsHeckeOn.unique {g : G} {T T' : Module.End ℂ (fixed π K)}
    (hT : IsHeckeOn π K g T) (hT' : IsHeckeOn π K g T') : T = T' := by sorry
