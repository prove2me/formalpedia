-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_full_linearized_representatives
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.full_linearized_representatives
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:35:47.135608+00:00
-- url     : https://prove2.me/theorems/5dad1123-0320-4f87-8f17-da9f2a1cafb6
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.full_linearized_representatives: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.full_linearized_representatives` of [lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialLinearized.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialLinearized.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology BigOperators`, `open JetPolynomial JetPolynomial.Perturbation PhaseMean`):
--
--   ```lean
--   theorem full_linearized_representatives {n : A.centers → ℕ}
--       (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
--       (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) :
--       ∃ Q : A.centers → Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
--         (∀ i k r, (Q i k r).SmoothCoeffs univ) ∧
--         A.PolynomialQuadraticRepresentation P Q ∧
--         A.PolynomialLinearRepresentation P Q
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.polynomialFamilyDegree` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PolynomialLinearRepresentation` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.PolynomialQuadraticRepresentation` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.Plane` and `OAI.ClosedSurfaceR4.planeModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_small_increment` and `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_compact_geometry_polynomial_increment` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/AtlasPolynomialLinearized.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.full_linearized_representatives)

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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAssemblyDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAssemblyFiberSpace
local instance polynomialAssemblyDualSmul_rd6e68b_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAssemblyFiberNormed
local instance polynomialAssemblySectionNormed_rd6e68b_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialAssemblySectionSpace_rd6e68b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem full_linearized_representatives {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) :
    ∃ Q : A.centers → Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ i k r, (Q i k r).SmoothCoeffs univ) ∧
      A.PolynomialQuadraticRepresentation P Q ∧
      A.PolynomialLinearRepresentation P Q := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
