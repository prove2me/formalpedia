-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isSmooth_smoothPart
-- name    : GroundTheory.Automorphic.isSmooth_smoothPart
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:35:57.382397+00:00
-- url     : https://prove2.me/theorems/1c3b67f1-6cf2-4a11-b490-81c1eb91f4be
-- title:
--   Automorphic: is Smooth smooth Part
-- statement:
--   The Automorphic construction uses the is Smooth smooth Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L203-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SmoothRep.lean#L203-L209

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

theorem GroundTheory.Automorphic.isSmooth_smoothPart : IsSmooth (smoothPart ρ) := by sorry
