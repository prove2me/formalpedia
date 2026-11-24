-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_fixedContragredientEquiv_apply
-- name    : GroundTheory.Automorphic.fixedContragredientEquiv_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:35.973632+00:00
-- url     : https://prove2.me/theorems/a8dcfdff-a7a9-43c3-9326-e87749e38439
-- title:
--   Automorphic: fixed Contragredient Equiv apply
-- statement:
--   The Automorphic construction uses the fixed Contragredient Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean#L139-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean#L139-L140

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
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
open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo

theorem GroundTheory.Automorphic.fixedContragredientEquiv_apply (x : fixedVectors (contragredient ρ) K) :
    fixedContragredientEquiv hρ hKc hKo x = restrictFixed ρ K x := by sorry
