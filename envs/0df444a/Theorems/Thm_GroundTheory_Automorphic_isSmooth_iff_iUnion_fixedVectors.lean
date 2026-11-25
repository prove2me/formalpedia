-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isSmooth_iff_iUnion_fixedVectors
-- name    : GroundTheory.Automorphic.isSmooth_iff_iUnion_fixedVectors
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:38.163898+00:00
-- url     : https://prove2.me/theorems/4ebcd3c1-463e-481c-ba48-6827a6893b7a
-- title:
--   Automorphic: is Smooth iff i Union fixed Vectors
-- statement:
--   The Automorphic construction uses the is Smooth iff i Union fixed Vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L239-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L239-L243

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

theorem GroundTheory.Automorphic.isSmooth_iff_iUnion_fixedVectors :
    IsSmooth ρ ↔ ⋃ (K : Subgroup G) (_ : IsCompact (K : Set G)) (_ : IsOpen (K : Set G)),
      (fixedVectors ρ K : Set V) = univ := by sorry
