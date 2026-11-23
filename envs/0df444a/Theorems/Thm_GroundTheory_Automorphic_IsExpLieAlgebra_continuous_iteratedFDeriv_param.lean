-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_iteratedFDeriv_param
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.continuous_iteratedFDeriv_param
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:44.927391+00:00
-- url     : https://prove2.me/theorems/0c31f59d-8fcd-4e6a-8d05-83f7b0bb0905
-- title:
--   Is Exp Lie Algebra: continuous iterated FDeriv param
-- statement:
--   The Is Exp Lie Algebra construction uses the continuous iterated FDeriv param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/Garding.lean#L30-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/Garding.lean#L30-L65

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.continuous_iteratedFDeriv_param {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (ψ : P → G → E')
    (hψ : ∀ g₀ : G, ContDiff ℝ ∞ (fun q : P × 𝔤 => ψ q.1 (g₀ * h.expG q.2))) (k : ℕ) :
    Continuous (fun p : P × G => iteratedFDeriv ℝ k (fun Y => ψ Y p.2) p.1) := by sorry
