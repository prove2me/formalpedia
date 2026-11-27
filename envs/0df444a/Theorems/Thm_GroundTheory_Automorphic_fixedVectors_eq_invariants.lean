-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_fixedVectors_eq_invariants
-- name    : GroundTheory.Automorphic.fixedVectors_eq_invariants
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:58.175507+00:00
-- url     : https://prove2.me/theorems/6188477e-e472-4310-97ad-7876ee11f519
-- title:
--   Automorphic: fixed Vectors eq invariants
-- statement:
--   The Automorphic construction uses the fixed Vectors eq invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L36-L39

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

theorem GroundTheory.Automorphic.fixedVectors_eq_invariants (H : Subgroup G) :
    fixedVectors ρ H = Representation.invariants (ρ.comp H.subtype) := by sorry
