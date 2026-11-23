-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_fixed_map_eq
-- name    : GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:01.193801+00:00
-- url     : https://prove2.me/theorems/c21b2ff2-b96d-445f-a3db-21ddb3221a42
-- title:
--   Iwahori Onto: exists fixed map eq
-- statement:
--   The Iwahori Onto construction uses the exists fixed map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L16-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L16-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IwahoriOnto
variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq {π : Representation ℂ G V} (hπ : IsSmooth π) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (f : V →ₗ[ℂ] W) (u : V) (hu : ∀ h ∈ H, f (π h u) = f u) :
    ∃ v ∈ fixed π H, f v = f u := by sorry
