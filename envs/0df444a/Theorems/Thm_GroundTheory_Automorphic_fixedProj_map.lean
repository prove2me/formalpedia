-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_fixedProj_map
-- name    : GroundTheory.Automorphic.fixedProj_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:08.59558+00:00
-- url     : https://prove2.me/theorems/f45b49e9-8836-493e-967a-55e5015f0db9
-- title:
--   Automorphic: fixed Proj map
-- statement:
--   The Automorphic construction uses the fixed Proj map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L382-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L382-L386

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
variable {ρ} {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo
omit hρ

theorem GroundTheory.Automorphic.fixedProj_map {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (f : Representation.IntertwiningMap ρ σ) (v : V) :
    fixedProj σ hσ hKc hKo (f v) = fixedMap ρ f K (fixedProj ρ hρ hKc hKo v) := by sorry
