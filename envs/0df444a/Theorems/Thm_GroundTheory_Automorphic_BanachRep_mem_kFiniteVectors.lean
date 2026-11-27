-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_BanachRep_mem_kFiniteVectors
-- name    : GroundTheory.Automorphic.BanachRep.mem_kFiniteVectors
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:57:11.978059+00:00
-- url     : https://prove2.me/theorems/52c69e34-b34b-54bb-8407-96da7b390173
-- title:
--   Banach Rep: mem k Finite Vectors
-- statement:
--   The Banach Rep construction uses the mem k Finite Vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/GKModule.lean#L156-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/GKModule.lean#L156-L156

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
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
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.BanachRep
variable {K' : Type*} [Group K'] [TopologicalSpace K']
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (π : BanachRep K' E) (K : Subgroup K')

theorem GroundTheory.Automorphic.BanachRep.mem_kFiniteVectors {v : E} : v ∈ π.kFiniteVectors K ↔ π.IsKFinite K v := by sorry
