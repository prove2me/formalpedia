-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_coe_fixedMap_apply
-- name    : GroundTheory.Automorphic.coe_fixedMap_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:34.110281+00:00
-- url     : https://prove2.me/theorems/a05e48ff-2969-4b93-a975-f4c31975d1e2
-- title:
--   Automorphic: coe fixed Map apply
-- statement:
--   The Automorphic construction uses the coe fixed Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L82-L84

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
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

theorem GroundTheory.Automorphic.coe_fixedMap_apply {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (f : Representation.IntertwiningMap ρ σ) (H : Subgroup G)
    (v : fixedVectors ρ H) : (fixedMap ρ f H v : W) = f v := by sorry
