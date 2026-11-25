-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_fixedProj_act_of_normalizes
-- name    : GroundTheory.Automorphic.Parabolic.fixedProj_act_of_normalizes
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:06.91988+00:00
-- url     : https://prove2.me/theorems/fc3d19c9-73c6-579d-b631-210db4f78e82
-- title:
--   Parabolic: fixed Proj act of normalizes
-- statement:
--   The Parabolic construction uses the fixed Proj act of normalizes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L20-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L20-L43

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
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
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}

theorem GroundTheory.Automorphic.Parabolic.fixedProj_act_of_normalizes (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {g : G} (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hg' : ∀ k ∈ K, g⁻¹ * k * g ∈ K) (v : V) :
    (fixedProj ρ hρ hKc hKo (ρ g v) : V) = ρ g (fixedProj ρ hρ hKc hKo v) := by sorry
