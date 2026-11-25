-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_smooth_density_prodExp
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.exists_smooth_density_prodExp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:21.152522+00:00
-- url     : https://prove2.me/theorems/54adc590-08e8-4ef6-8a86-a880b1ab34ea
-- title:
--   Is Exp Lie Algebra: exists smooth density prod Exp
-- statement:
--   The Is Exp Lie Algebra construction uses the exists smooth density prod Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarDensity.lean#L18-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarDensity.lean#L18-L92

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaar
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarDensity
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
open MeasureTheory Metric Set Filter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
  [μ.IsHaarMeasure]

theorem GroundTheory.Automorphic.IsExpLieAlgebra.exists_smooth_density_prodExp {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ K : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ K → tsupport K ⊆ closedBall 0 ε →
      ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧
        HasCompactSupport κ ∧
        ∀ φ : G → ℂ, Continuous φ → ∫ y, κ y * φ y ∂μ = ∫ t, K t * φ (h.prodExp (⇑b) t) := by sorry
