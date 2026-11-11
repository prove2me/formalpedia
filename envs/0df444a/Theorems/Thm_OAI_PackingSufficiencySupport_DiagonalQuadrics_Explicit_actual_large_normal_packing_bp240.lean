-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_actual_large_normal_packing_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_large_normal_packing_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:51:08.904325+00:00
-- url     : https://prove2.me/theorems/0c27c118-045e-42ba-8a83-dc35534f3f3b
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_large_normal_packing_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_large_normal_packing` of [lean/OAI/Geometry/BallPacking/Models/LiouvilleRadialCalculus.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Models/LiouvilleRadialCalculus.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit`, with `open scoped ContDiff Manifold Topology BigOperators Pointwise`, `open Set Function Filter Manifold MeasureTheory`, `open Hamiltonian MomentPolytope`):
--
--   ```lean
--   theorem actual_large_normal_packing_bp240 (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
--       (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
--       (hrr : ∀ i,r' i < r i) {a₀ : ℝ} (ha₀ : 0<a₀) (ha₁ : a₀<1)
--       (hrs : ∀ i,r i<1-a₀) (hhalf : ∀ i,r i<1/2)
--       (hvol : ∑ i,r i^(m+4)<1-a₀^(m+4)) :
--       ∃ h₁ h₂ d₁ d₂ : ℚ, (∀ i,r i<h₁) ∧ h₁<d₁ ∧ (d₁:ℝ)<1-a₀ ∧
--         (∀ i,r i<h₂) ∧ h₂<d₂ ∧ (d₂:ℝ)<1/2 ∧
--         ∃ ℓ,∃ φ : Fin N → Ambient (m+4) → Surface m × PlanePhase (Fin (m+3)),
--           (∀ i,FormNeighborhoodEmbedding (closedBall (m+4) (r' i))
--             (fun _ => successorStandardForm (m+3))
--             (globalHorizontalCoupling phaseArea
--               (largeHorizontalPrimitive (q := m+2) (parameters m) ∘ planeMoments)) (φ i)) ∧
--           (∀ i,MapsTo (φ i) (closedBall (m+4) (r' i))
--             (interior (projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ) ×ˢ
--               planeRegion (largeModelBounds (m+2) h₂) ![h₁,h₂]))) ∧
--           Pairwise (fun i j => Disjoint (φ i '' closedBall (m+4) (r' i))
--             (φ j '' closedBall (m+4) (r' j)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Ambient`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exhaustionRadius`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.locus`, `OAI.PackingSufficiencySupport.Hamiltonian.FormNeighborhoodEmbedding`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseArea`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_injective` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.closedBall` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.Surface` (definitions bundle `OAIQ240Bp009` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.globalHorizontalCoupling` and `OAI.PackingSufficiencySupport.Hamiltonian.planeMoments` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.projectionDomain` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.largeModelBounds`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.largeHorizontalPrimitive`, `OAI.PackingSufficiencySupport.Hamiltonian.successorStandardForm` and `OAI.PackingSufficiencySupport.MomentPolytope.planeRegion` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.actual_complement_packing_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Models/LiouvilleRadialCalculus.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_large_normal_packing)

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

namespace Explicit

 attribute [local instance] OAI.PackingSufficiencySupport.DiagonalQuadrics.liouvilleRadialSigmaCompact
theorem actual_large_normal_packing_bp240 (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) {a₀ : ℝ} (ha₀ : 0<a₀) (ha₁ : a₀<1)
    (hrs : ∀ i,r i<1-a₀) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+4)<1-a₀^(m+4)) :
    ∃ h₁ h₂ d₁ d₂ : ℚ, (∀ i,r i<h₁) ∧ h₁<d₁ ∧ (d₁:ℝ)<1-a₀ ∧
      (∀ i,r i<h₂) ∧ h₂<d₂ ∧ (d₂:ℝ)<1/2 ∧
      ∃ ℓ,∃ φ : Fin N → Ambient (m+4) → Surface m × PlanePhase (Fin (m+3)),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+4) (r' i))
          (fun _ => successorStandardForm (m+3))
          (globalHorizontalCoupling phaseArea
            (largeHorizontalPrimitive (q := m+2) (parameters m) ∘ planeMoments)) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall (m+4) (r' i))
          (interior (projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ) ×ˢ
            planeRegion (largeModelBounds (m+2) h₂) ![h₁,h₂]))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+4) (r' i))
          (φ j '' closedBall (m+4) (r' j))) := by
  sorry

end Explicit

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
end
