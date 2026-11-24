-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_fixedMap_injective
-- name    : GroundTheory.Automorphic.fixedMap_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:21:29.076423+00:00
-- url     : https://prove2.me/theorems/aa896da6-abf7-4c11-9e65-6641b63d04a9
-- title:
--   Automorphic: fixed Map injective
-- statement:
--   The Automorphic construction uses the fixed Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L146-L149

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

theorem GroundTheory.Automorphic.fixedMap_injective {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} {K : Subgroup G} {f : Representation.IntertwiningMap ρ σ}
    (hf : Function.Injective f) : Function.Injective (fixedMap ρ f K) := by sorry
