-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_BanachRep_coe_apply
-- name    : GroundTheory.Automorphic.BanachRep.coe_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:57.606621+00:00
-- url     : https://prove2.me/theorems/b0c75ec1-0164-5ea5-90c9-0f496929d8ce
-- title:
--   Banach Rep: coe apply
-- statement:
--   The Banach Rep construction uses the coe apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/SmoothVectors.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/SmoothVectors.lean#L28-L28

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.BanachRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (π : BanachRep G E)

theorem GroundTheory.Automorphic.BanachRep.coe_apply (g : G) : π g = π.toHom g := by sorry
