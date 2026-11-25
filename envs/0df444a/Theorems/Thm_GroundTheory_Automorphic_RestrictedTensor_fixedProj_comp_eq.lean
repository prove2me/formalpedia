-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_fixedProj_comp_eq
-- name    : GroundTheory.Automorphic.RestrictedTensor.fixedProj_comp_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:08.282263+00:00
-- url     : https://prove2.me/theorems/9e7645d7-b492-4451-94cb-ae88ec1a25fe
-- title:
--   Restricted Tensor: fixed Proj comp eq
-- statement:
--   The Restricted Tensor construction uses the fixed Proj comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L191-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Window.lean#L191-L209

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
omit hρ hKc hKo

theorem GroundTheory.Automorphic.RestrictedTensor.fixedProj_comp_eq {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L] (ι : L →* G)
    (hρ : IsSmooth ρ) (hρι : IsSmooth (ρ.comp ι)) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {K' : Subgroup L} (hK'c : IsCompact (K' : Set L))
    (hK'o : IsOpen (K' : Set L)) (hK' : ∀ k ∈ K', ι k ∈ K) {u : V}
    (hu : ∀ h ∈ K, ∃ k ∈ K', ρ h u = ρ (ι k) u) :
    (fixedProj (ρ.comp ι) hρι hK'c hK'o u : V) = fixedProj ρ hρ hKc hKo u := by sorry
