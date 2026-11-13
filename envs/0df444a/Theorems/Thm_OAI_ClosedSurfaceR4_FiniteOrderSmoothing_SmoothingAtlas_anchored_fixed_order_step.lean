-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_anchored_fixed_order_step
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_fixed_order_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:40:44.60654+00:00
-- url     : https://prove2.me/theorems/3c90ad2f-81c9-479b-99f9-d1404576467e
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_fixed_order_step: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_fixed_order_step` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/AnchoredFixedOrderStep.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/AnchoredFixedOrderStep.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators NNReal`, `open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry MetricGoodPhaseData`):
--
--   ```lean
--   theorem anchored_fixed_order_step (g : SmoothMetric M)
--       (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
--       (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
--       ∃ z₀ a D : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧
--       ∀ k : ℕ, 10 ≤ k → ∀ Budget : ℝ → ℝ, HasPolynomialBound Budget →
--       ∃ ε : ℝ → ℝ, ∃ P L : ℕ → ℝ → ℝ,
--         HasPolynomialBound (fun x => (ε x)⁻¹) ∧
--         (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (L m)) ∧
--         (∀ x, 1 ≤ x → 0 < ε x ∧ ε x ≤ 1) ∧
--       ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
--         ContMDiff planeModel spaceModel ∞ F →
--         (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
--         (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
--           ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
--           c ≤ NormalFrame.gramDet
--             (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
--             (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
--           b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
--       ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
--       ∀ t : ℝ, 0 < t → t < ε z⁻¹ → ∀ j : ℕ, k ≤ j → j ≤ k+1 →
--         A.InputBound t (40*(k+1)) (Budget z⁻¹) G (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
--         A.WeightedBound 1 2 ((z^4/D)/4) (G-F) →
--         (∀ x, ‖A.tensorEncode (normalizedTensorDefect g.inner (t^(k : ℝ)) G) x-A.tensorEncode g.inner x‖ ≤ a/8) →
--         ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
--           (∀ m, A.WeightedBound (t^(6/5 : ℝ)) m (P m z⁻¹*(t^(k : ℝ)*t^(6/5 : ℝ))) U) ∧
--           (∀ m ≤ k/2, A.WeightedBound 1 m ((z^4/D)*t) U) ∧
--           ∀ m C, 0 ≤ C → A.InputBound t m C G (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
--             A.TensorWeightedBound (t^(6/5 : ℝ)) m (L m z⁻¹*(1+Budget z⁻¹+C)*t^(1/5 : ℝ))
--               (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U)-g.inner)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.chartWeightCompact` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.HasPolynomialBound` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorPlaneRead` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.RealModes.TangentPair` and `OAI.ClosedSurfaceR4.RealModes.firstJetPair` (definitions bundle `OAIQ249SI006` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredFixedFiberNormed` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.normalizedTensorDefect`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.InputBound`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorEncode` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_prepared_correction` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/AnchoredFixedOrderStep.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_fixed_order_step)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry MetricGoodPhaseData
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredFixedFiberNormed
local instance anchoredFixedFiberSpace_r109dc5_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance anchoredFixedDualAdd_r109dc5_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance anchoredFixedDualSmul_r109dc5_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance anchoredFixedSectionNormed_r109dc5_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance anchoredFixedSectionSpace_r109dc5_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem anchored_fixed_order_step (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ z₀ a D : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧
    ∀ k : ℕ, 10 ≤ k → ∀ Budget : ℝ → ℝ, HasPolynomialBound Budget →
    ∃ ε : ℝ → ℝ, ∃ P L : ℕ → ℝ → ℝ,
      HasPolynomialBound (fun x => (ε x)⁻¹) ∧
      (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (L m)) ∧
      (∀ x, 1 ≤ x → 0 < ε x ∧ ε x ≤ 1) ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
    ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
    ∀ t : ℝ, 0 < t → t < ε z⁻¹ → ∀ j : ℕ, k ≤ j → j ≤ k+1 →
      A.InputBound t (40*(k+1)) (Budget z⁻¹) G (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
      A.WeightedBound 1 2 ((z^4/D)/4) (G-F) →
      (∀ x, ‖A.tensorEncode (normalizedTensorDefect g.inner (t^(k : ℝ)) G) x-A.tensorEncode g.inner x‖ ≤ a/8) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound (t^(6/5 : ℝ)) m (P m z⁻¹*(t^(k : ℝ)*t^(6/5 : ℝ))) U) ∧
        (∀ m ≤ k/2, A.WeightedBound 1 m ((z^4/D)*t) U) ∧
        ∀ m C, 0 ≤ C → A.InputBound t m C G (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
          A.TensorWeightedBound (t^(6/5 : ℝ)) m (L m z⁻¹*(1+Budget z⁻¹+C)*t^(1/5 : ℝ))
            (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U)-g.inner) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
