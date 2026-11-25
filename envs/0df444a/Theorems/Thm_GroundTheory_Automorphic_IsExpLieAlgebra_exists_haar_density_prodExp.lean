-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_haar_density_prodExp
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.exists_haar_density_prodExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:01.47526+00:00
-- url     : https://prove2.me/theorems/a651cf90-2cc9-414f-92ab-35bfaf17b253
-- title:
--   Is Exp Lie Algebra: exists haar density prod Exp
-- statement:
--   The Is Exp Lie Algebra construction uses the exists haar density prod Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaar.lean#L17-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaar.lean#L17-L444

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaar
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
open NormedSpace Set Filter MeasureTheory Metric
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
  [μ.IsHaarMeasure]

theorem GroundTheory.Automorphic.IsExpLieAlgebra.exists_haar_density_prodExp {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ (r : ℝ) (ρ : (Fin d → ℝ) → ℝ) (c : G → (Fin d → ℝ)) (W : Set G), 0 < r ∧
      ContDiff ℝ ∞ ρ ∧ (∀ z ∈ ball (0 : Fin d → ℝ) r, 0 < ρ z) ∧ IsOpen W ∧
      (∀ z ∈ ball (0 : Fin d → ℝ) r, h.prodExp (⇑b) z ∈ W ∧ c (h.prodExp (⇑b) z) = z) ∧
      (∀ y ∈ W, h.prodExp (⇑b) (c y) = y) ∧
      (∀ g ∈ W, ContDiffAt ℝ ∞ (fun Y : 𝔤 => c (g * h.expG Y)) 0) ∧
      ∀ ψ₀ : G → ℂ, Continuous ψ₀ → HasCompactSupport ψ₀ →
        tsupport ψ₀ ⊆ h.prodExp (⇑b) '' ball 0 r →
        ∫ y, ψ₀ y ∂μ = ∫ z in ball (0 : Fin d → ℝ) r, ψ₀ (h.prodExp (⇑b) z) * (ρ z : ℂ) := by sorry
