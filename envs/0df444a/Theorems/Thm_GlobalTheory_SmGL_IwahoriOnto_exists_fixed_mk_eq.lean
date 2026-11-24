-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IwahoriOnto_exists_fixed_mk_eq
-- name    : GlobalTheory.SmGL.IwahoriOnto.exists_fixed_mk_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:57.209686+00:00
-- url     : https://prove2.me/theorems/3f29f299-58ba-488c-a87d-9e48cdc2979c
-- title:
--   Iwahori Onto: exists fixed mk eq
-- statement:
--   The Iwahori Onto construction uses the exists fixed mk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L52-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IwahoriProjSurjective.lean#L52-L92

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

theorem GlobalTheory.SmGL.IwahoriOnto.exists_fixed_mk_eq {π : Representation ℂ G V} (hπ : IsAdmissible π) {I N : Subgroup G}
    (ho : IsOpen (I : Set G)) (hc : IsCompact (I : Set G)) {M : Type} [CommGroup M] (s : M →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (M₀ : Subgroup M) (hM₀ : ∀ d ∈ M₀, s d ∈ I)
    (C : Set G) (hfac : ∀ g ∈ I, ∃ d ∈ M₀, ∃ x ∈ N, ∃ c ∈ C, g = s d * x * c)
    (hcon : ∀ U ∈ 𝓝 (1 : G), ∃ t : M, ∀ c ∈ C, (s t)⁻¹ * c * s t ∈ U)
    (y : Jacquet π N) (hy : y ∈ fixed (jacquet π N s hs) M₀) :
    ∃ v ∈ fixed π I, (twKer π N 1).mkQ v = y := by sorry
