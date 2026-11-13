-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_mode_quadrature
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_mode_quadrature
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:32:52.740441+00:00
-- url     : https://prove2.me/theorems/d6f391bf-6bb6-4222-a25a-dd85b65cfa13
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_mode_quadrature: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_mode_quadrature` of [lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialModeMean.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialModeMean.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean`):
--
--   ```lean
--   theorem polynomial_mode_quadrature {n : A.centers → ℕ} {m : ℕ}
--       (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
--       (Q : A.centers → Fin 3 → Fin m → Expression)
--       (hrep : A.PolynomialQuadraticRepresentation P Q)
--       (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
--       (φ : M → ℝ) (Z : M → Fin 4 → ℂ)
--       (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
--       (hZ : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ Z) :
--       A.atlasPolynomialQuadratic P ε F (spaceCoordinates.symm ∘ surfaceMode τ φ Z)+
--         A.atlasPolynomialQuadratic P ε F
--           (spaceCoordinates.symm ∘ surfaceMode τ φ (fun p => Complex.I • Z p)) =
--         (2 : ℝ) • A.polynomialModeMean Q F ε τ φ Z
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.spaceCoordinates` and `OAI.ClosedSurfaceR4.RealModes.RVec` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.surfaceMode` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.modeMeanDualAdd` (definitions bundle `OAIQ249SI008` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PolynomialQuadraticRepresentation` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlasPolynomialQuadratic` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomialModeMean` (definitions bundle `OAIQ249SI011` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_mode_mean` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialModeMean.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_mode_quadrature)

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
import Definitions.Def_OAIQ249SI011

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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.modeMeanDualAdd
local instance modeMeanFiberNormed_rd48cb7_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance modeMeanFiberSpace_rd48cb7_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance modeMeanDualSmul_rd48cb7_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance modeMeanSectionNormed_rd48cb7_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance modeMeanSectionSpace_rd48cb7_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_mode_quadrature {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : M → ℝ) (Z : M → Fin 4 → ℂ)
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ Z) :
    A.atlasPolynomialQuadratic P ε F (spaceCoordinates.symm ∘ surfaceMode τ φ Z)+
      A.atlasPolynomialQuadratic P ε F
        (spaceCoordinates.symm ∘ surfaceMode τ φ (fun p => Complex.I • Z p)) =
      (2 : ℝ) • A.polynomialModeMean Q F ε τ φ Z := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
