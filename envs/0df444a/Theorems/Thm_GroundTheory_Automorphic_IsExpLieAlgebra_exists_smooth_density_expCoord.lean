-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_smooth_density_expCoord
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.exists_smooth_density_expCoord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:35.14033+00:00
-- url     : https://prove2.me/theorems/a5605ddd-814e-486f-b716-a42b78f4f24d
-- title:
--   Is Exp Lie Algebra: exists smooth density exp Coord
-- statement:
--   The Is Exp Lie Algebra construction uses the exists smooth density exp Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpHaar.lean#L120-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpHaar.lean#L120-L289

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarDensity
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
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
variable (h : IsExpLieAlgebra G 𝔤)
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

theorem GroundTheory.Automorphic.IsExpLieAlgebra.exists_smooth_density_expCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ β : EuclideanSpace ℝ (Fin d) → ℂ, ContDiff ℝ ∞ β →
      tsupport β ⊆ closedBall 0 ε →
      ∃ κ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ κ) ∧
        HasCompactSupport κ ∧ tsupport κ ⊆ (fun x => h.expG (coordEquiv b x)) '' tsupport β ∧
        ∀ φ : G → ℂ, Continuous φ →
          ∫ y, κ y * φ y ∂μ = ∫ x, β x * φ (h.expG (coordEquiv b x)) := by sorry
