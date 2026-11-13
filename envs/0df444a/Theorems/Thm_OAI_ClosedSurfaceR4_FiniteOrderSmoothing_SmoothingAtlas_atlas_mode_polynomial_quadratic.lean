-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_mode_polynomial_quadratic
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_mode_polynomial_quadratic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:33:44.396521+00:00
-- url     : https://prove2.me/theorems/200b0978-1f8f-4b1b-8f92-c9adc4777ea7
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_mode_polynomial_quadratic: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_mode_polynomial_quadratic` of [lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasModePolynomialQuadratic.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasModePolynomialQuadratic.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean`):
--
--   ```lean
--   theorem atlas_mode_polynomial_quadratic {n : A.centers → ℕ} {m : ℕ}
--       {ι : Type*} [Fintype ι] [DecidableEq ι]
--       (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
--       (Q : A.centers → Fin 3 → Fin m → Expression)
--       (hrep : A.PolynomialQuadraticRepresentation P Q)
--       (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
--       (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
--       (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
--       (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j)) :
--       A.atlasPolynomialQuadratic P ε F
--           (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) =
--         A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
--           coordinateQuadraticMean (Q i) ε (A.jetChartMap i F)
--             (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 x)+
--         A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
--           ∑ l : RealModes.QuadraticLabel ι,
--             QuadraticMean.displacement τ
--               (RealModes.quadraticPhase (fun j => coordinatePhase (A.vectorChartRead i (φ j))) l)
--               (coordinateQuadraticCoefficient (Q i) ε (A.jetChartMap i F)
--                 (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 l) x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression` and `OAI.ClosedSurfaceR4.QuadraticMean.RVec` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.QuadraticLabel` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.planeWeight`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorPlaneRestore`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.vectorChartRead` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePhase` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.surfaceMode` and `OAI.ClosedSurfaceR4.QuadraticMean.displacement` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinateQuadraticCoefficient` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinateQuadraticMean` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.modePolynomialDualAdd` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PolynomialQuadraticRepresentation` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialQuadratic` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.RealModes.quadraticPhase` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.jetChartMap` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_input_global_polynomial_quadratic_cancellation_all_profiles` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.input_polynomial_free_correction_fixed_phase` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasModePolynomialQuadratic.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_mode_polynomial_quadratic)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Definitions.Def_OAIQ249SI010

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.modePolynomialDualAdd
local instance modePolynomialFiberNormed_r677524_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance modePolynomialFiberSpace_r677524_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance modePolynomialDualSmul_r677524_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance modePolynomialSectionNormed_r677524_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance modePolynomialSectionSpace_r677524_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem atlas_mode_polynomial_quadratic {n : A.centers → ℕ} {m : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j)) :
    A.atlasPolynomialQuadratic P ε F
        (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) =
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        coordinateQuadraticMean (Q i) ε (A.jetChartMap i F)
          (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 x)+
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ
            (RealModes.quadraticPhase (fun j => coordinatePhase (A.vectorChartRead i (φ j))) l)
            (coordinateQuadraticCoefficient (Q i) ε (A.jetChartMap i F)
              (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 l) x) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
