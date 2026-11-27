-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exact_fixedMap
-- name    : GroundTheory.Automorphic.exact_fixedMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:44.146625+00:00
-- url     : https://prove2.me/theorems/c07ea462-5caf-4a14-b62a-9b46c1128bbb
-- title:
--   Automorphic: exact fixed Map
-- statement:
--   The Automorphic construction uses the exact fixed Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L395-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L395-L410

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
variable {W X : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
  {ρ} {σ : Representation ℂ G W} {τ : Representation ℂ G X} {K : Subgroup G}

theorem GroundTheory.Automorphic.exact_fixedMap (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {f : Representation.IntertwiningMap ρ σ}
    {g : Representation.IntertwiningMap σ τ} (hfg : Function.Exact f g) :
    Function.Exact (fixedMap ρ f K) (fixedMap σ g K) := by sorry
