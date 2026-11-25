-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_GKModule_subQuot_rep
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.GKModule.subQuot_rep
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:11.695117+00:00
-- url     : https://prove2.me/theorems/fb85ac41-3ac0-4bc2-b35e-a62fd456e12f
-- title:
--   GKModule: sub Quot rep
-- statement:
--   The GKModule construction uses the sub Quot rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/CoeToRepresentationApply.lean#L197-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/CoeToRepresentationApply.lean#L197-L199

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
variable (M : h.GKModule K V) (U : Subrepresentation M.rep) (U₀ : Submodule ℂ U.toSubmodule)
  (hU₀ : ∀ a, U₀ ≤ U₀.comap (U.toRepresentation a))

theorem GroundTheory.Automorphic.IsExpLieAlgebra.GKModule.subQuot_rep : (M.subQuot U U₀ hU₀).rep = quotRep M U U₀ hU₀ := by sorry
