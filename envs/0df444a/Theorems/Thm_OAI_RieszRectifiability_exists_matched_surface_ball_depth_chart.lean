-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_exists_matched_surface_ball_depth_chart
-- name    : OAI.RieszRectifiability.exists_matched_surface_ball_depth_chart
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:24:34.016187+00:00
-- url     : https://prove2.me/theorems/3fd0fbb8-d6a3-43d5-995f-f4c81830b274
-- title:
--   OAI.RieszRectifiability.exists_matched_surface_ball_depth_chart: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.exists_matched_surface_ball_depth_chart` of [lean/OAI/Analysis/RieszRectifiability/Surfaces/MatchedSurfaceBallDepthCharts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Surfaces/MatchedSurfaceBallDepthCharts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set Filter Topology`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem exists_matched_surface_ball_depth_chart (hn : 0 < n) (J : ℕ)
--       (r : ℝ) (hr : 0 < r) (a : Ambient d) :
--       ∃ g : ball (0 : Ambient n) r → Ambient d,
--         LipschitzWith (finiteBallChartUnionConstant d (11 ^ d)
--           (projectionRegionDepthConstant d (Real.toNNReal (2 / κ)) J)) g ∧
--         Set.range g ⊆ closedBall a (3 * r) ∧
--         (μH[(n : ℝ)] : Measure (Ambient d)) ((A ∩ closedBall a (3 * r)) \ Set.range g) ≤
--           (ENNReal.ofReal (1 - nativeCoreAreaFraction n G)) ^ J * ENNReal.ofReal (G * (8 * r) ^ n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.finiteBallChartUnionConstant`, `OAI.RieszRectifiability.nativeCoreAreaFraction`, `OAI.RieszRectifiability.nativeSurfaceArea`, `OAI.RieszRectifiability.projectionRegionDepthConstant` and `OAI.RieszRectifiability.projectionStopShadowConstant` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.AdmissibleRadius` and `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.quantitative_uniform_restart_surface_pieces` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Surfaces/MatchedSurfaceBallDepthCharts.lean (declaration OAI.RieszRectifiability.exists_matched_surface_ball_depth_chart)

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

variable {n d : ℕ}
    (ν : Measure (Ambient d)) (A : Set (Ambient d)) (hν : ν = nativeSurfaceArea n A)
    (hsupport : ν.support = A)
    (C G : ℝ) (hC : 0 < C) (hG : 0 < G) (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (σ κ : ℝ) (hσ : 0 < σ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hwidth : σ + κ ≤ 1) (hsmall : 2048 * σ * (κ + 1) ≤ κ)
    (hshadow : projectionStopShadowConstant n C σ κ ≤ nativeCoreAreaFraction n G)
    (hgeometry : ∀ p ∈ ν.support, ∀ r : ℝ, 0 < r →
      ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
        (∀ x ∈ ν.support ∩ closedBall p (1024 * r),
          infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤ σ * r) ∧
        closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
          P.orthogonalProjectionOnto '' (ν.support ∩ closedBall p (r / 16)))
    (hdiam : ediam ν.support = ⊤)

include hν hsupport hC hG hg hlower hσ hκ hκ1 hwidth hsmall hshadow hgeometry hdiam

theorem exists_matched_surface_ball_depth_chart (hn : 0 < n) (J : ℕ)
    (r : ℝ) (hr : 0 < r) (a : Ambient d) :
    ∃ g : ball (0 : Ambient n) r → Ambient d,
      LipschitzWith (finiteBallChartUnionConstant d (11 ^ d)
        (projectionRegionDepthConstant d (Real.toNNReal (2 / κ)) J)) g ∧
      Set.range g ⊆ closedBall a (3 * r) ∧
      (μH[(n : ℝ)] : Measure (Ambient d)) ((A ∩ closedBall a (3 * r)) \ Set.range g) ≤
        (ENNReal.ofReal (1 - nativeCoreAreaFraction n G)) ^ J * ENNReal.ofReal (G * (8 * r) ^ n) := by
  sorry

end

end RieszRectifiability

end OAI
end
