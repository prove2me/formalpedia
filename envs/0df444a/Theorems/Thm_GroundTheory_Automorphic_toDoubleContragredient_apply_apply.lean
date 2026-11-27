-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_toDoubleContragredient_apply_apply
-- name    : GroundTheory.Automorphic.toDoubleContragredient_apply_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:08.389801+00:00
-- url     : https://prove2.me/theorems/231dfce4-cb4d-42bf-a08d-2495b526caf0
-- title:
--   Automorphic: to Double Contragredient apply apply
-- statement:
--   The Automorphic construction uses the to Double Contragredient apply apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRepContragredient.lean#L97-L100

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

theorem GroundTheory.Automorphic.toDoubleContragredient_apply_apply (hρ : IsSmooth ρ) (v : V)
    (x : smoothVectors (Representation.dual ρ)) :
    ((toDoubleContragredient hρ v : smoothVectors (Representation.dual (contragredient ρ))) :
      Module.Dual ℂ (smoothVectors (Representation.dual ρ))) x = (x : Module.Dual ℂ V) v := by sorry
