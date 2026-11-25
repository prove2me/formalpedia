-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdU_mul
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.AdU_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:02.945578+00:00
-- url     : https://prove2.me/theorems/6feda4fe-dc32-4ae1-b73b-3d7ee444623d
-- title:
--   Is Exp Lie Algebra: Ad U mul
-- statement:
--   The Is Exp Lie Algebra construction uses the Ad U mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean#L50-L56

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.AdU_mul (g g' : G) : h.AdU (g * g') = (h.AdU g).comp (h.AdU g') := by sorry
