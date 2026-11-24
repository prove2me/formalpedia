-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem_coinvariantsKer
-- name    : GroundTheory.Automorphic.fixedProj_apply_of_mem_coinvariantsKer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:52.92815+00:00
-- url     : https://prove2.me/theorems/5ae1b9fe-3b36-4eb7-b157-8c44af8bfb0c
-- title:
--   Automorphic: fixed Proj apply of mem coinvariants Ker
-- statement:
--   The Automorphic construction uses the fixed Proj apply of mem coinvariants Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L342-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L342-L344

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

theorem GroundTheory.Automorphic.fixedProj_apply_of_mem_coinvariantsKer {v : V} (hv : v ∈ coinvariantsKer ρ K) :
    fixedProj ρ hρ hKc hKo v = 0 := by sorry
