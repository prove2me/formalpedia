-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_largeHorizontalPrimitive_area_limit_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.largeHorizontalPrimitive_area_limit_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:53:38.630204+00:00
-- url     : https://prove2.me/theorems/5ddac808-951f-4391-9485-13243fb6311c
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.largeHorizontalPrimitive_area_limit_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.largeHorizontalPrimitive_area_limit` of [lean/OAI/Geometry/BallPacking/Models/LiouvilleRadialCalculus.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Models/LiouvilleRadialCalculus.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics`, with `open scoped ContDiff Manifold Topology BigOperators Pointwise`, `open Set Function Filter Manifold MeasureTheory`, `open Hamiltonian MomentPolytope`):
--
--   ```lean
--   theorem largeHorizontalPrimitive_area_limit_bp240 {h₁ h₂ : ℝ} (hh₁ : h₁<1) (hh₂ : h₂<1/2) :
--       TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral
--         (projectionDomain_compact a (exhaustionRadius a ℓ))
--         (fun x => largeNormalCoefficient q p • curveFSForm a (1/Real.pi) x))
--         (fun p => (2:ℝ)^m*largeNormalCoefficient q p) atTop
--         (region (largeModelBounds q h₂) ![h₁,h₂])
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exhaustionRadius`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.largeNormalCoefficient` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.locus` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.MomentPolytope.region` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.compactSurfaceFormIntegral` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.projectionDomain`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.projectionDomain_compact` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.largeModelBounds`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.curveFSForm`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.liouvilleRadialSigmaCompact` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceManifold` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_large_normal_packing_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Models/LiouvilleRadialCalculus.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.largeHorizontalPrimitive_area_limit)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open Hamiltonian MomentPolytope

 variable {m q : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

 attribute [local instance] OAI.PackingSufficiencySupport.DiagonalQuadrics.liouvilleRadialSigmaCompact
theorem largeHorizontalPrimitive_area_limit_bp240 {h₁ h₂ : ℝ} (hh₁ : h₁<1) (hh₂ : h₂<1/2) :
    TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral
      (projectionDomain_compact a (exhaustionRadius a ℓ))
      (fun x => largeNormalCoefficient q p • curveFSForm a (1/Real.pi) x))
      (fun p => (2:ℝ)^m*largeNormalCoefficient q p) atTop
      (region (largeModelBounds q h₂) ![h₁,h₂]) := by
  sorry

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end
