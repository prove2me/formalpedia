-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdU_inv_apply
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.AdU_inv_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:08:08.083436+00:00
-- url     : https://prove2.me/theorems/95ec2466-ef8f-453d-b9fb-7b1a7af91a3a
-- title:
--   Is Exp Lie Algebra: Ad U inv apply
-- statement:
--   The Is Exp Lie Algebra construction uses the Ad U inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean#L67-L69

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
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
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.AdU_inv_apply (g : G) (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    h.AdU g⁻¹ (h.AdU g u) = u := by sorry
