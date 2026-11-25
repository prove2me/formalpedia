-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_GKModule_rep_comm
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.GKModule.rep_comm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:31:44.068933+00:00
-- url     : https://prove2.me/theorems/574ff4ad-37d1-4d7b-b4be-068ef6b21e2d
-- title:
--   GKModule: rep comm
-- statement:
--   The GKModule construction uses the rep comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/CoeToRepresentationApply.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/CoeToRepresentationApply.lean#L33-L43

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CoeToRepresentationApply
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
attribute [local instance 100] LieRing.ofAssociativeRing
open Set Module
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G} {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem GroundTheory.Automorphic.IsExpLieAlgebra.GKModule.rep_comm (M : h.GKModule K V) {T : End ℂ V} (hρ : ∀ X, M.ρ X * T = T * M.ρ X)
    (hσ : ∀ k, M.σ k * T = T * M.σ k) (a : FreeMonoid (h.lieSubalgebra ⊕ K)) :
    M.rep a * T = T * M.rep a := by sorry
