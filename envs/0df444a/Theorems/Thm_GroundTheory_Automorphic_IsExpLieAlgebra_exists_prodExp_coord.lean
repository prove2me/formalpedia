-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_prodExp_coord
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.exists_prodExp_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:10.50511+00:00
-- url     : https://prove2.me/theorems/dd3e702a-0cb4-4f6e-aa00-47e97eee6ef4
-- title:
--   Is Exp Lie Algebra: exists prod Exp coord
-- statement:
--   The Is Exp Lie Algebra construction uses the exists prod Exp coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L145-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L145-L192

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {G : Subgroup 𝔸ˣ} (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.exists_prodExp_coord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ (S T : Set (Fin d → ℝ)) (ψ : (Fin d → ℝ) → (Fin d → ℝ)), IsOpen S ∧ IsOpen T ∧
      (0 : Fin d → ℝ) ∈ S ∧ MapsTo (prodExpCoord b) S T ∧ MapsTo ψ T S ∧
      (∀ z ∈ S, ψ (prodExpCoord b z) = z) ∧ (∀ w ∈ T, prodExpCoord b (ψ w) = w) ∧
      ContDiffOn ℝ ∞ ψ T ∧ (∀ z ∈ S, prodExpVal (fun i => (b i : 𝔸)) z ∈ h.nhdOne) := by sorry
