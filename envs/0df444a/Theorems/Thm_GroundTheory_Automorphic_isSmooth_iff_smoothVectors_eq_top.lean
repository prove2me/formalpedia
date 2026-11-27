-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isSmooth_iff_smoothVectors_eq_top
-- name    : GroundTheory.Automorphic.isSmooth_iff_smoothVectors_eq_top
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:42.446372+00:00
-- url     : https://prove2.me/theorems/19402d2c-9bc9-49c8-acbc-fc2fa8157e5d
-- title:
--   Automorphic: is Smooth iff smooth Vectors eq top
-- statement:
--   The Automorphic construction uses the is Smooth iff smooth Vectors eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L178-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L178-L180

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
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]

theorem GroundTheory.Automorphic.isSmooth_iff_smoothVectors_eq_top : IsSmooth ρ ↔ smoothVectors ρ = ⊤ := by sorry
