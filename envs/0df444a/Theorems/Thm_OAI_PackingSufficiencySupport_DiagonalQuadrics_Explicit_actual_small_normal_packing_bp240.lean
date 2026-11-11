-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_Explicit_actual_small_normal_packing_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_small_normal_packing_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:51:20.980932+00:00
-- url     : https://prove2.me/theorems/57a69cc6-ccd7-48c4-9c59-f903d0329b7c
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_small_normal_packing_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_small_normal_packing` of [lean/OAI/Geometry/BallPacking/Models/RationalSlack.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Models/RationalSlack.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit`, with `open scoped ContDiff Manifold Topology BigOperators Pointwise`, `open Set Function Filter Manifold MeasureTheory`, `open Hamiltonian MomentPolytope`):
--
--   ```lean
--    theorem actual_small_normal_packing_bp240 (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
--       (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
--       (hrr : ∀ i,r' i < r i) (hhalf : ∀ i,r i<1/2)
--       (hvol : ∑ i,r i^(m+3)<1) :
--       ∃ h d : ℚ, (∀ i,r i<h) ∧ h<d ∧ (d:ℝ)<1/2 ∧
--         ∃ ℓ,∃ φ : Fin N → Ambient (m+3) → Surface m × PlanePhase (Fin (m+2)),
--           (∀ i,FormNeighborhoodEmbedding (closedBall (m+3) (r' i))
--             (fun _ => successorStandardForm (m+2))
--             (globalHorizontalCoupling phaseArea
--               (normalHorizontalPrimitive (parameters m) 2 ∘ planeMoments)) (φ i)) ∧
--           (∀ i,MapsTo (φ i) (closedBall (m+3) (r' i))
--             (interior (projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ) ×ˢ
--               (planeMoments ⁻¹' momentSimplex (m+2) h)))) ∧
--           Pairwise (fun i j => Disjoint (φ i '' closedBall (m+3) (r' i))
--             (φ j '' closedBall (m+3) (r' j)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Ambient`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.exhaustionRadius`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.locus`, `OAI.PackingSufficiencySupport.Hamiltonian.FormNeighborhoodEmbedding`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.phaseArea`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_injective` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.momentSimplex` (definitions bundle `OAIQ240Bp004` of this split); `OAI.PackingSufficiencySupport.closedBall` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.Surface` (definitions bundle `OAIQ240Bp009` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.globalHorizontalCoupling` and `OAI.PackingSufficiencySupport.Hamiltonian.planeMoments` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.projectionDomain` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalHorizontalPrimitive` and `OAI.PackingSufficiencySupport.Hamiltonian.successorStandardForm` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.main_theorem` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Models/RationalSlack.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.actual_small_normal_packing)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open Hamiltonian MomentPolytope

 theorem actual_small_normal_packing_bp240 (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0 < r i) (hr' : ∀ i,0 ≤ r' i)
    (hrr : ∀ i,r' i < r i) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+3)<1) :
    ∃ h d : ℚ, (∀ i,r i<h) ∧ h<d ∧ (d:ℝ)<1/2 ∧
      ∃ ℓ,∃ φ : Fin N → Ambient (m+3) → Surface m × PlanePhase (Fin (m+2)),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+3) (r' i))
          (fun _ => successorStandardForm (m+2))
          (globalHorizontalCoupling phaseArea
            (normalHorizontalPrimitive (parameters m) 2 ∘ planeMoments)) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall (m+3) (r' i))
          (interior (projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ) ×ˢ
            (planeMoments ⁻¹' momentSimplex (m+2) h)))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+3) (r' i))
          (φ j '' closedBall (m+3) (r' j))) := by
  sorry

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

end

end OAI
end
