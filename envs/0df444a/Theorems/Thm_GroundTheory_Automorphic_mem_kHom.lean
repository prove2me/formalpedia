-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_kHom
-- name    : GroundTheory.Automorphic.mem_kHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:54:02.654374+00:00
-- url     : https://prove2.me/theorems/0a664f91-2e71-5105-bb7a-00b987391049
-- title:
--   Automorphic: mem k Hom
-- statement:
--   The Automorphic construction uses the mem k Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/GKModule.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/GKModule.lean#L28-L29

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
variable {K : Type*} [Monoid K]
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem GroundTheory.Automorphic.mem_kHom {τ : Representation ℂ K W} {σ : Representation ℂ K V} {T : W →ₗ[ℂ] V} :
    T ∈ kHom τ σ ↔ ∀ k : K, T ∘ₗ τ k = σ k ∘ₗ T := by sorry
