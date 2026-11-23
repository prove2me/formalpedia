-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_contDiff_comp_expG_mul_expG
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.contDiff_comp_expG_mul_expG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:13.272583+00:00
-- url     : https://prove2.me/theorems/2ba6ad8e-0771-4903-b954-b1dc9bd3a541
-- title:
--   Is Exp Lie Algebra: cont Diff comp exp G mul exp G
-- statement:
--   The Is Exp Lie Algebra construction uses the cont Diff comp exp G mul exp G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/Garding.lean#L74-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/Garding.lean#L74-L83

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.contDiff_comp_expG_mul_expG {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : G → F} (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, F) ∞ f)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ₁ φ₂ : V → 𝔤}
    (h₁ : ContDiff ℝ ∞ φ₁) (a : G) (h₂ : ContDiff ℝ ∞ φ₂) :
    ContDiff ℝ ∞ (fun p => f (h.expG (φ₁ p) * a * h.expG (φ₂ p))) := by sorry
