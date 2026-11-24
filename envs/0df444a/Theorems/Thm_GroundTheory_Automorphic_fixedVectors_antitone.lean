-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_fixedVectors_antitone
-- name    : GroundTheory.Automorphic.fixedVectors_antitone
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:37.421528+00:00
-- url     : https://prove2.me/theorems/df36a92b-e418-4586-8925-4c0a3c13a6ca
-- title:
--   Automorphic: fixed Vectors antitone
-- statement:
--   The Automorphic construction uses the fixed Vectors antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L41-L43

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

theorem GroundTheory.Automorphic.fixedVectors_antitone {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) :
    fixedVectors ρ H₂ ≤ fixedVectors ρ H₁ := by sorry
