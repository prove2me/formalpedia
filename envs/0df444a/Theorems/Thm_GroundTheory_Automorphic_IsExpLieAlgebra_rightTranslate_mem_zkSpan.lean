-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_rightTranslate_mem_zkSpan
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.rightTranslate_mem_zkSpan
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:23.059799+00:00
-- url     : https://prove2.me/theorems/0faf410e-05ad-45b7-aae0-7da8b4aa1e7e
-- title:
--   Is Exp Lie Algebra: right Translate mem zk Span
-- statement:
--   The Is Exp Lie Algebra construction uses the right Translate mem zk Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean#L235-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean#L235-L248

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
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable (K : Subgroup G)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.rightTranslate_mem_zkSpan (f : h.smoothFuns (F := F)) (k' : K)
    {w : h.smoothFuns (F := F)} (hw : w ∈ h.zkSpan K f) :
    h.rightTranslateEnd (k' : G) w ∈ h.zkSpan K f := by sorry
