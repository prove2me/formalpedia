-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isSmooth_contragredient
-- name    : GroundTheory.Automorphic.isSmooth_contragredient
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:16.065317+00:00
-- url     : https://prove2.me/theorems/4515e932-25c5-4f13-9d6f-f3128c336092
-- title:
--   Automorphic: is Smooth contragredient
-- statement:
--   The Automorphic construction uses the is Smooth contragredient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean#L51-L52

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
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.Automorphic.isSmooth_contragredient : IsSmooth (contragredient ρ) := by sorry
